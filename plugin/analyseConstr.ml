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

(* map in the order of memory representation *)
let map_ltr f c =
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

let annotate_constr ~verbose info c =
  let info = ref info in
  let map = ref Int.Map.empty in
  let as_var s =
    let s = Id.of_string_soft ("(* "^s^" *)") in
    mkVar s
  in
  let annot s c = mkApp (as_var s, [|c|]) in
  let rec aux c =
    let i', cinf = ANA.step !info in
    info := i';
    match cinf with
    | Fresh idx ->
      let c' = map_ltr aux c in
      map := Int.Map.add idx (c,c',ref 1) !map;
      annot ("fresh " ^ string_of_int idx) c'
    | Seen idx ->
      match Int.Map.find_opt idx !map with
      | None -> annot ("MISSING seen " ^ string_of_int idx) c
      | Some (c',_,refcnt) ->
        incr refcnt;
        if c != c' then CErrors.anomaly Pp.(str "mismatch when annotating")
        else if verbose then annot ("seen " ^string_of_int idx) c
        else as_var ("seen " ^ string_of_int idx)
  in
  let c = aux c in
  let map = Int.Map.map (fun (c,c',refcnt) -> c,c',!refcnt) !map in
  !info, map, c

let rec tree_size_aux cnt c =
  Constr.fold tree_size_aux (cnt+1) c

let tree_size c = tree_size_aux 0 c

let graph_size info c =
  let info = ref info in
  let cnt = ref 0 in
  let rec graph_size_aux c =
    let i', cinf = ANA.step !info in
    info := i';
    match cinf with
    | Fresh _ ->
      incr cnt;
      iter_ltr graph_size_aux c
    | Seen _ -> ()
  in
  graph_size_aux c;
  !cnt
