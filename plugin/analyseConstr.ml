open Util
open Names

module ANA = RocqSharingAnalyser.SharingAnalyser

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

let slist x = let open ANA in cofix (fun x_slist -> sum [|[|x;x_slist|];[|ignore;x_slist|]|])

let constr_descr =
  let open ANA in
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

let analyse_constr (c:Constr.t) = ANA.analyse constr_descr (Obj.repr c)

let analyse_econstr c = analyse_constr (EConstr.Unsafe.to_constr c)

open Constr

(* iterate in the order of memory representation
   (identical to Constr.iter currently but we don't want to rely on that) *)
let iter_ltr f c = match kind c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _ | Int _ | Float _ | String _) -> ()
  | Cast (c,_,t) -> f c; f t
  | Prod (_,t,c) -> f t; f c
  | Lambda (_,t,c) -> f t; f c
  | LetIn (_,b,t,c) -> f b; f t; f c
  | App (c,l) -> f c; Array.iter f l
  | Proj (_p,_r,c) -> f c
  | Evar (_,l) -> SList.Skip.iter f l
  | Case (_,_,pms,p,iv,c,bl) ->
    Array.iter f pms; f (snd @@ fst p); iter_invert f iv; f c; Array.iter (fun (_, b) -> f b) bl
  | Fix (_,(_,tl,bl)) -> Array.iter f tl; Array.iter f bl
  | CoFix (_,(_,tl,bl)) -> Array.iter f tl; Array.iter f bl
  | Array(_u,t,def,ty) -> Array.iter f t; f def; f ty

let map_invert f = function
  | NoInvert -> NoInvert
  | CaseInvert {indices} -> CaseInvert {indices=Array.map f indices}

let map_under_context f d =
  let (nas, p) = d in
  let p' = f p in
  (nas, p')

let map_branches f bl =
  let bl' = Array.map (map_under_context f) bl in
  bl'

let map_return_predicate f (p,r) =
  let p' = map_under_context f p in
  p', r

(* map in the order of memory representation *)
let map_kind_ltr f c =
  match c with
  | (Rel _ | Meta _ | Var _   | Sort _ | Const _ | Ind _
    | Construct _ | Int _ | Float _ | String _) as k -> k
  | Cast (b,k,t) ->
      let b' = f b in
      let t' = f t in
      Cast (b', k, t')
  | Prod (na,t,b) ->
      let t' = f t in
      let b' = f b in
      Prod (na, t', b')
  | Lambda (na,t,b) ->
      let t' = f t in
      let b' = f b in
      Lambda (na, t', b')
  | LetIn (na,b,t,k) ->
      let b' = f b in
      let t' = f t in
      let k' = f k in
      LetIn (na, b', t', k')
  | App (b,l) ->
      let b' = f b in
      let l' = Array.map f l in
      App (b', l')
  | Proj (p,r,t) ->
      let t' = f t in
      Proj (p, r, t')
  | Evar (e,l) ->
      let l' = SList.Skip.map f l in
      Evar (e, l')
  | Case (ci,u,pms,p,iv,b,bl) ->
      let pms' = Array.map f pms in
      let p' = map_return_predicate f p in
      let iv' = map_invert f iv in
      let b' = f b in
      let bl' = map_branches f bl in
      Case (ci, u, pms', p', iv', b', bl')
  | Fix (ln,(lna,tl,bl)) ->
      let tl' = Array.map f tl in
      let bl' = Array.map f bl in
      Fix (ln,(lna,tl',bl'))
  | CoFix(ln,(lna,tl,bl)) ->
      let tl' = Array.map f tl in
      let bl' = Array.map f bl in
      CoFix (ln,(lna,tl',bl'))
  | Array(u,t,def,ty) ->
    let t' = Array.map f t in
    let def' = f def in
    let ty' = f ty in
    Array(u,t',def',ty')

type 'a kind_gen = ('a,'a,Sorts.t,UVars.Instance.t,Sorts.relevance) kind_of_term

type annotated = {
  self : constr;
  kind : annotated kind_gen;
  uid : int;
}

type 'a annotate = {
  fresh : int -> constr -> 'a kind_gen -> 'a;
  seen : int -> constr -> 'a -> 'a;
}

type 'a annotation_result = {
  subterms : (Constr.t * 'a * int) Int.Map.t;
  order : int list;
  root : 'a;
}

let annotate_constr_gen annotate info c =
  let info = ref info in
  let map = ref Int.Map.empty in
  let order = ref [] in
  let rec aux c =
    let i', cinf = ANA.step !info in
    info := i';
    match cinf with
    | Fresh idx ->
      let k = map_kind_ltr aux @@ Constr.kind c in
      let c' = annotate.fresh idx c k in
      if Int.Map.mem idx !map then CErrors.anomaly Pp.(str "present Fresh when annotating");
      map := Int.Map.add idx (c,c',ref 1) !map;
      order := idx :: !order;
      c'
    | Seen idx ->
      match Int.Map.find_opt idx !map with
      | None -> CErrors.anomaly Pp.(str "missing Seen when annotating")
      | Some (c',annotated,refcnt) ->
        incr refcnt;
        if c != c' then CErrors.anomaly Pp.(str "mismatch when annotating")
        else annotate.seen idx c annotated
  in
  let c = aux c in
  let map = Int.Map.map (fun (c,c',refcnt) -> c,c',!refcnt) !map in
  !info, { subterms = map; order = List.rev !order; root = c }

let constr_annotate = {
  fresh = (fun idx c k -> { self = c; kind = k; uid = idx });
  seen = (fun _ _ x -> x);
}

let annotate_constr = annotate_constr_gen constr_annotate

let debug_annotate ~verbose =
  let as_var s idx =
    let s = Id.of_string_soft ("(* "^s^" "^string_of_int idx^" *)") in
    mkVar s
  in
  let annot s idx c = mkApp (as_var s idx, [|c|]) in
  {
    fresh = (fun idx c k -> annot "fresh" idx (Constr.of_kind k));
    seen = (fun idx c _ ->
        if verbose then annot "seen" idx c
        else as_var "seen" idx);
  }

let debug_annotate_constr ~verbose = annotate_constr_gen (debug_annotate ~verbose)

let rec tree_size_aux cnt c =
  Constr.fold tree_size_aux (cnt+1) c

let tree_size c = tree_size_aux 0 c

let graph_size info c =
  let info = ref info in
  let cnt = ref 0 in
  let edge_cnt = ref 0 in
  let rec graph_size_aux c =
    let i', cinf = ANA.step !info in
    incr edge_cnt;
    info := i';
    match cinf with
    | Fresh _ ->
      incr cnt;
      iter_ltr graph_size_aux c
    | Seen _ -> ()
  in
  graph_size_aux c;
  !cnt, !edge_cnt
