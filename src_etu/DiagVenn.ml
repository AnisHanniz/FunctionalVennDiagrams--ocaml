
open Formule_Log_Prop
open Formule_Syllogisme

(* open Formule_Log_Prop *)

module Predicate_set = Set.Make (String)
(** Module des ensembles de prédicats représentés par des chaines de caractères *)

(** Type des remplissages possibles d'un diagramme de Venn *)
type remplissage = Vide | NonVide
module Diag = Map.Make (Predicate_set)
(** Module des Maps dont les clés sont des ensembles de chaînes de caractères *)

type diagramme = remplissage Diag.t
(** Type des diagrammes de Venn *)

(** AF string_of_diag d : conversion d'un diagramme d en une chaîne de caractères *)
let string_of_diag (d : diagramme) : string =
  let string_of_set s =
    let elements = Predicate_set.elements s in
    let set_str = String.concat ", " elements in
    if set_str = "" then "∅" else "{" ^ set_str ^ "}"
  in
  Diag.fold
    (fun k v acc ->
       acc ^ string_of_set k ^ " -> " ^
       (match v with
       | Vide -> "Vide"
       | NonVide -> "NonVide") ^ "\n"
    ) d ""

  
(** AF diag_from_formule alpha f : construit le diagramme de Venn associé à la formule f sur
      les prédicats issus de f ou de alpha *)

let diag_from_formule (alpha : string list) (f : formule_syllogisme) :
  diagramme list =
match f with 
  | PourTout(p) -> let tab = table_verite alpha p in 
    let d = Diag.empty in 
      let d = List.fold_left (fun acc e -> 
        match e with 
        | (l, false) -> Diag.add (Predicate_set.of_list l) Vide acc
        | _ -> acc) d tab in 
        [d]
      | IlExiste(p) -> let tab = table_verite alpha p in
        List.fold_left (fun acc e -> 
          match e with 
          | (l, true) -> (Diag.add (Predicate_set.of_list l) NonVide Diag.empty) :: acc
          | _ -> acc) [] tab   

(** AF conj_diag d1 d2 : Calcule la combinaison/conjonction de deux diagrammes, 
    renvoyant None si incompatibilité *)
let conj_diag (d1 : diagramme) (d2 : diagramme) : diagramme option =
  let combined_diagram = Diag.fold (fun k v acc ->
    match acc with
    | None -> None
    | Some acc' ->
      match Diag.find_opt k d2 with
      | None -> Some (Diag.add k v acc')
      | Some v2 ->
        if v2 = v then Some (Diag.add k v2 acc')
        else None
    ) d1 (Some Diag.empty) in
      
    match combined_diagram with
    | None -> None
    | Some acc -> Some (Diag.fold (fun k v acc -> Diag.add k v acc) d2 acc)
    

(** AF est_compatible_diag_diag dp dc : teste si le diagramme dp d'une prémisse est compatible
    avec le diagramme dc d'une conclusion *)
let est_compatible_diag_diag (dp : diagramme) (dc : diagramme) : bool =
  Diag.fold (fun k v acc ->
    acc && match Diag.find_opt k dp with
      | None -> false
      | Some pred ->
        match v, pred with
        | Vide, Vide -> true
        | NonVide, NonVide -> true
        | _ -> false
      ) dc true
    
(** AF est_compatible_diag_list dp dcs : teste si un diagramme dp d'une prémisse est compatible
    avec un des diagrammes de la liste dcs,
    diagrammes issus d'une conclusion *)
let est_compatible_diag_list (dp : diagramme) (dcs : diagramme list) : bool =
      List.exists (fun e -> est_compatible_diag_diag dp e) dcs
    
(** AF est_compatible_list_list dps dcs : teste si chacun des diagrammes de dps, diagrammes issus de prémisses,
    est compatible avec au moins un des diagrammes de dcs, diagrammes issus d'une conclusion *)
let est_compatible_list_list (dps : diagramme list) (dcs : diagramme list) : bool =
  List.for_all (fun e -> est_compatible_diag_list e dcs) dps


(** AF atome_dans_formules f : La liste des atomes qui sont présent dans la liste 
    de formule_syllogisme *)
let atome_dans_formules (f : formule_syllogisme list) : string list =
  let atome_dans_f = function
    | PourTout p | IlExiste p -> atome_dans_f p
    in
    let rec collect_atoms acc = function
      | [] -> acc
      | formule :: rest ->
        let atoms = atome_dans_f formule in
        let new_atoms = List.filter (fun a -> not (List.mem a acc)) atoms in
        collect_atoms (new_atoms @ acc) rest
    in
    List.rev (collect_atoms [] f)
    
(** fusion_pourtout_diag_list dl : renvoie un diagramme qui représente tous les éléments de 
    dl et qui ont pour valeur "Vide" *)
let fusion_pourtout_diag_list (dl : diagramme list) : diagramme = 
  List.fold_left (fun acc e -> 
    Diag.fold (fun k v acc' -> 
      if v = Vide then Diag.add k v acc' else acc') e acc) (Diag.empty) dl

(** combinaison ps : la combinaison des diagrammes *)
let combinaison (ps : formule_syllogisme list) : diagramme list = 
  let alpha = atome_dans_formules ps in 
  let fus = fusion_pourtout_diag_list 
    (List.flatten (List.map (diag_from_formule alpha) ps)) in
  let rec aux l acc = 
    match l with 
    | [] -> acc 
    | e :: l' -> 
      match e with 
      | PourTout(_) -> aux l' acc 
      | IlExiste(_) -> let d = diag_from_formule alpha e in
        List.fold_left (fun acc' e' -> 
          match conj_diag e' fus with 
          | None -> acc'
          | Some e'' -> e'' :: acc') acc d in
  let r = aux ps [] in 
  if r = [] then [fus] else r

(** AF est_compatible_premisses_conc ps c : teste si une liste de prémisses ps est compatible avec une conclusion c *)
let est_compatible_premisses_conc (ps : formule_syllogisme list)
    (c : formule_syllogisme) : bool =
    let alpha = atome_dans_formules ps in 
    let dps = combinaison ps in 
    let dc = diag_from_formule alpha c in
    est_compatible_list_list dps dc


(** AF temoin_incompatibilite_premisses_conc_opt ps c : renvoie un diagramme de la
    combinaison des prémisses ps incompatible avec la conclusion c s'il existe, 
    None sinon **)
let temoin_incompatibilite_premisses_conc_opt (ps : formule_syllogisme list)
      (c : formule_syllogisme) : diagramme option =
    let alpha = atome_dans_formules ps in 
    let dps = combinaison ps in
    let dc = diag_from_formule alpha c in
    let rec aux l = 
      match l with 
      | [] -> None 
      | e :: l' -> 
        if est_compatible_diag_list e dc then aux l' else Some e 
    in aux dps

(** AF temoins_incompatibilite_premisses_conc ps c : renvoie les diagrammes de la 
    combinaison des prémisses ps incompatibles avec la conclusion c *)
let temoins_incompatibilite_premisses_conc (ps : formule_syllogisme list) 
    (c : formule_syllogisme) : diagramme list = 
    let alpha = atome_dans_formules ps in 
    let dps = combinaison ps in
    let dc = diag_from_formule alpha c in
    let rec aux l acc = 
      match l with 
      | [] -> acc 
      | e :: l' -> 
        if est_compatible_diag_list e dc then aux l' acc else aux l' (e::acc) in 
    aux dps [] 
