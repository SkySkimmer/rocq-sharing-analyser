open Util
open Names

module Analyser = RocqSharingAnalyser.SharingAnalyser

module ConstrRepr = struct
(** Copy of constr types so that we remember to update the descr when the type changes *)

type case_info = Constr.case_info
type cast_kind = Constr.cast_kind

type ('na,'r) pbinder_annot = ('na, 'r) Context.pbinder_annot

type ('constr, 'types, 'r) prec_declaration =
    (Name.t,'r) pbinder_annot array * 'types array * 'constr array
type ('constr, 'types, 'r) pfixpoint =
    (int array * int) * ('constr, 'types, 'r) prec_declaration
type ('constr, 'types, 'r) pcofixpoint =
    int * ('constr, 'types, 'r) prec_declaration

type 'constr pcase_invert = 'constr Constr.pcase_invert =
  | NoInvert
  | CaseInvert of { indices : 'constr array }

type ('constr,'r) pcase_branch = (Name.t,'r) Context.pbinder_annot array * 'constr
type ('types,'r) pcase_return = ((Name.t,'r) Context.pbinder_annot array * 'types) * 'r

type ('constr, 'types, 'sort, 'univs, 'r) kind_of_term = ('constr, 'types, 'sort, 'univs, 'r) Constr.kind_of_term =
  | Rel       of int
  | Var       of Id.t
  | Meta      of int
  | Evar      of (Evar.t * 'constr SList.t)
  | Sort      of 'sort
  | Cast      of 'constr * cast_kind * 'types
  | Prod      of (Name.t,'r) pbinder_annot * 'types * 'types
  | Lambda    of (Name.t,'r) pbinder_annot * 'types * 'constr
  | LetIn     of (Name.t,'r) pbinder_annot * 'constr * 'types * 'constr
  | App       of 'constr * 'constr array
  | Const     of (Constant.t * 'univs)
  | Ind       of (inductive * 'univs)
  | Construct of (constructor * 'univs)
  | Case      of case_info * 'univs * 'constr array * ('types,'r) pcase_return * 'constr pcase_invert * 'constr * ('constr,'r) pcase_branch array
  | Fix       of ('constr, 'types, 'r) pfixpoint
  | CoFix     of ('constr, 'types, 'r) pcofixpoint
  | Proj      of Projection.t * 'r * 'constr
  | Int       of Uint63.t
  | Float     of Float64.t
  | String    of Pstring.t
  | Array     of 'univs * 'constr array * 'constr * 'types
[@@warning "-34"]

let constr_descr =
  let open Analyser in
  cofix (fun constr ->
  remember @@ sum [|
    (* Rel *) [|ignore|];
    (* Var *) [|ignore|];
    (* Meta *) [|ignore|];
    (* Evar *) [|tuple [|ignore;slist constr|]|];
    (* Sort *) [|ignore|];
    (* Cast *) [|constr;ignore;constr|];
    (* Prod *) [|ignore;constr;constr|];
    (* Lambda *) [|ignore;constr;constr|];
    (* LetIn *) [|ignore;constr;constr;constr|];
    (* App *) [|constr;array constr|];
    (* Const *) [|ignore|];
    (* Ind *) [|ignore|];
    (* Construct *) [|ignore|];
    (* Case *)
    [|ignore(*ci*);
      ignore(*u*);
      array constr(*pms*);
      pair (pair ignore constr) ignore(*return*);
      sum [|[|array constr|]|](*case_invert*);
      constr(*head*);
      array (pair ignore constr)(*branches*);
    |];
    (* Fix *) [|pair ignore (tuple [|ignore;array constr;array constr|])|];
    (* CoFix *) [|pair ignore (tuple [|ignore;array constr;array constr|])|];
    (* Proj *) [|ignore;ignore;constr|];
    (* Int *) [|ignore|];
    (* Float *) [|ignore|];
    (* String *) [|ignore|];
    (* Array *) [|ignore;array constr;constr;constr|];
  |])
end

let constr_descr = ConstrRepr.constr_descr

let analyse_constr (c:Constr.t) = Analyser.analyse constr_descr (Obj.repr c)

let pr_rec_analysis x =
  let open Pp in
  let open Analyser in
  let l = to_list x in
  let pr_one = function
    | Fresh n -> str "Fresh " ++ int n
    | Seen n -> str "Seen " ++ int n
  in
  hov 1 (str "[" ++ prlist_with_sep pr_comma pr_one l ++ str "]")

(* map in the order of memory representation *)
let map_ltr f c =
  let open Constr in
  match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _ | Int _ | Float _ | String _) -> c
  | Cast (b,k,t) ->
      let b' = f b in
      let t' = f t in
      if b'==b && t' == t then c
      else mkCast (b', k, t')
  | Prod (na,t,b) ->
      let t' = f t in
      let b' = f b in
      if b'==b && t' == t then c
      else mkProd (na, t', b')
  | Lambda (na,t,b) ->
      let t' = f t in
      let b' = f b in
      if b'==b && t' == t then c
      else mkLambda (na, t', b')
  | LetIn (na,b,t,k) ->
      let b' = f b in
      let t' = f t in
      let k' = f k in
      if b'==b && t' == t && k'==k then c
      else mkLetIn (na, b', t', k')
  | App (b,l) ->
      let b' = f b in
      let l' = Array.Smart.map f l in
      if b'==b && l'==l then c
      else mkApp (b', l')
  | Proj (p,r,t) ->
      let t' = f t in
      if t' == t then c
      else mkProj (p, r, t')
  | Evar (e,l) ->
      let l' = SList.Smart.map f l in
      if l'==l then c
      else mkEvar (e, l')
  | Case (ci,u,pms,p,iv,b,bl) ->
      let pms' = Array.Smart.map f pms in
      let p' = map_return_predicate f p in
      let iv' = map_invert f iv in
      let b' = f b in
      let bl' = map_branches f bl in
      if b'==b && iv'==iv && p'==p && bl'==bl && pms'==pms then c
      else mkCase (ci, u, pms', p', iv', b', bl')
  | Fix (ln,(lna,tl,bl)) ->
      let tl' = Array.Smart.map f tl in
      let bl' = Array.Smart.map f bl in
      if tl'==tl && bl'==bl then c
      else mkFix (ln,(lna,tl',bl'))
  | CoFix(ln,(lna,tl,bl)) ->
      let tl' = Array.Smart.map f tl in
      let bl' = Array.Smart.map f bl in
      if tl'==tl && bl'==bl then c
      else mkCoFix (ln,(lna,tl',bl'))
  | Array(u,t,def,ty) ->
    let t' = Array.Smart.map f t in
    let def' = f def in
    let ty' = f ty in
    if def'==def && t==t' && ty==ty' then c
    else mkArray(u,t',def',ty')

let annotate_constr info c =
  let open Constr in
  let info = ref info in
  let map = ref Int.Map.empty in
  let annot s c =
    let s = Id.of_string_soft ("(* "^s^" *)") in
    mkApp (mkVar s, [|c|])
  in
  let rec aux c =
    let i', cinf = Analyser.step !info in
    info := i';
    match cinf with
    | Fresh idx ->
      map := Int.Map.add idx c !map;
      let c = map_ltr aux c in
      annot ("fresh " ^ string_of_int idx) c
    | Seen idx ->
      match Int.Map.find_opt idx !map with
      | None -> annot ("MISSING seen " ^ string_of_int idx) c
      | Some c' -> if c != c' then annot ("MISMATCH seen " ^ string_of_int idx) c
        else annot ("seen " ^ string_of_int idx) c
  in
  let c = aux c in
  !info, !map, c

let warn_not_done = CWarnings.create ~name:"sharing-analysis-mismatch"
    Pp.(fun () -> str "Analysis mismatch (not fully consumed)!")

let pp_with_info env sigma info c =
  let info, map, c = annotate_constr info c in
  let msg =
    let open Pp in
    let pr_constr c = Printer.pr_constr_env env sigma c in
    let is_done = Analyser.is_done info in
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

let rocq_type n = KerName.make Ltac2_plugin.Tac2env.coq_prefix (Label.make n)

let t_constr = rocq_type "constr"

let do_ltac2_constr_analysis ~pstate tac =
  let open Ltac2_plugin in
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
