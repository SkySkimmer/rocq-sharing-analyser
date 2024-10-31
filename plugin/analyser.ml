open Names
open AnalyseConstr

module ANA = RocqSharingAnalyser.SharingAnalyser

let pr_rec_analysis x =
  let open Pp in
  let open ANA in
  let l = to_list x in
  let pr_one = function
    | Fresh n -> str "Fresh " ++ int n
    | Seen n -> str "Seen " ++ int n
  in
  hov 1 (str "[" ++ prlist_with_sep pr_comma pr_one l ++ str "]")

let warn_not_done = CWarnings.create ~name:"sharing-analysis-mismatch"
    Pp.(fun () -> str "Analysis mismatch (not fully consumed)!")

let pp_with_info env sigma info c =
  let info, map, c = annotate_constr info c in
  let msg =
    let open Pp in
    let pr_constr c = Printer.pr_constr_env env sigma c in
    let is_done = ANA.is_done info in
    let () = if not is_done then warn_not_done () in
    pr_constr c ++ fnl() ++ fnl() ++
    str "subterms:" ++ fnl() ++
    prlist_with_sep fnl (fun (i,c) -> int i ++ str " ==> " ++ pr_constr c)
      (Int.Map.bindings map)
  in
  msg

let get_current_context_opt pstate =
  match pstate with
    | None ->
      let env = Global.env() in
      Evd.from_env env, env
    | Some pstate -> Declare.Proof.get_current_context pstate

let do_constr_analysis ~pstate c =
  let sigma, env = get_current_context_opt pstate in
  let flags = Pretyping.all_no_fail_flags in
  let c = Constrintern.intern_constr env sigma c in
  let sigma, c = Pretyping.understand_tcc ~flags env sigma c in
  let c = EConstr.Unsafe.to_constr c in
  let info = analyse_constr c in
  let msg = pp_with_info env sigma info c in
  Feedback.msg_info msg

let do_proof_analysis ~pstate =
  let p = Declare.Proof.get pstate in
  let { Proof.sigma } = Proof.data p in
  let c = Proof.partial_proof p in
  let c = match c with
    | [c] -> c
    | _ -> CErrors.user_err Pp.(str "Analysis of multi statement proofs not supported.")
  in
  let c = Evarutil.nf_evar sigma c in
  let c = EConstr.Unsafe.to_constr c in
  let info = analyse_constr c in
  (* NB we want global env not goal env here *)
  let msg = pp_with_info (Global.env()) sigma info c in
  Feedback.msg_info msg

let do_def_body_analysis ~opaque_access qid =
  let kn = Nametab.locate_constant qid in
  match Global.body_of_constant opaque_access kn with
  | None -> CErrors.user_err Pp.(Libnames.pr_qualid qid ++ str " does not have a body.")
  | Some (c, _, _) ->
    (* XXX handle poly and private univs*)
    let env = Global.env() in
    let sigma = Evd.from_env env in
    let info = analyse_constr c in
    let msg = pp_with_info env sigma info c in
    Feedback.msg_info msg

open Ltac2_plugin

let rocq_type n = KerName.make Tac2env.coq_prefix (Label.make n)

let t_constr = rocq_type "constr"

let do_ltac2_constr_analysis ~pstate tac =
  let open Tac2expr in
  let loc = tac.CAst.loc in
  let tac = CAst.make ?loc (CTacCnv (tac, CAst.make ?loc (CTypRef (AbsKn (Other t_constr), [])))) in
  let tac, _ = Tac2intern.intern ~strict:false [] tac in
  let tac = Tac2interp.interp Tac2interp.empty_environment tac in
  let env = Global.env () in
  let selector, proof =
    match pstate with
    | None ->
      let sigma = Evd.from_env env in
      let name, poly = Id.of_string "ltac2", false in
      Goal_select.SelectAll, Proof.start ~name ~poly sigma []
    | Some pstate ->
      Goal_select.get_default_goal_selector (),
      Declare.Proof.get pstate
  in
    let nosuchgoal =
    let info = Exninfo.reify () in
    Proofview.tclZERO ~info (Proof.SuggestNoSuchGoals (1,proof))
  in
  let tac = Goal_select.tclSELECT ~nosuchgoal selector tac in
  let (proof, _, ans) = Proof.run_tactic (Global.env ()) tac proof in
  let { Proof.sigma } = Proof.data proof in
  let c = Tac2ffi.to_constr ans in
  let c = EConstr.Unsafe.to_constr c in
  let info = analyse_constr c in
  let msg = pp_with_info env sigma info c in
  Feedback.msg_info msg

open Tac2ffi
open Tac2externals

let pname s = { Tac2expr.mltac_plugin = "rocq-sharing-analyser.plugin"; mltac_tactic = s }

let define s spec f = Tac2externals.define (pname s) spec f

let () = define "hcons" (constr @-> ret constr) @@ fun c ->
  let c = EConstr.Unsafe.to_constr c in
  let c = Constr.hcons c in
  EConstr.of_constr c
