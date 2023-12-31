
open Formule_Log_Prop
open Formule_Syllogisme
open DiagVenn

let a = Atome "a"
let b = Atome "b"
let c = Atome "c"
let d = Atome "d"
let p1 = PourTout (Imp (Ou (a, b), c))
let p2 = PourTout (Imp (c, Ou (a, b)))
let p3 = IlExiste a
let p4 = IlExiste (Imp (a, Non b))
let p5 = PourTout (Imp (Xor (a, b), c))
let p6 = PourTout (Imp (Non c, a))
let c1 = IlExiste b
let c2 = IlExiste c
let c3 = IlExiste d

(** AF test premisses conclusion : teste si chacun des diagrammes de la combinaison
    de la liste prémisses est compatible avec au moins un des diagrammes de conclusion,
    tout en traçant les calculs réalisés et les diagrammes calculés,
    et en affichant tous les contre-exemples le cas échéant. *)

let string_of_diagrams_list str_dl =
  let rec string_of_diag_list str_dl s i =
    match str_dl with
    | [] -> s
    | h :: t ->
      string_of_diag_list t (s ^ "Diagramme " ^ string_of_int i ^ " :\n" ^ h ^ "\n") (i + 1)
    in
      string_of_diag_list str_dl "" 1
    
let string_of_premises str_dps =
  let rec string_of_premisses str_dps s i =
    match str_dps with
    | [] -> s
    | h :: t ->
    string_of_premisses t (s ^ "Diagrammes de la prémisse " ^ string_of_int i ^ " :\n" ^ string_of_diagrams_list h ^ "\n") (i + 1)
    in
    string_of_premisses str_dps "" 1
    
let test (ps : formule_syllogisme list) (c : formule_syllogisme) : unit =
  let alpha = atome_dans_formules ps in
  let dps = List.map (diag_from_formule alpha) ps in
  let str_dps = List.map (List.map string_of_diag) dps in
  let str_dc = List.map string_of_diag (diag_from_formule alpha c) in
  let comb = List.map string_of_diag (combinaison ps) in
  let premises_str = string_of_premises str_dps in
  let s =
    "\tPrémisses :\n" ^ List.fold_left (fun s p -> s ^ string_of_formule p ^ "\n") "" ps ^
    "\tConclusion :\n" ^ string_of_formule c ^ "\n" ^
    "\tDiagrammes de chaque prémisse :\n" ^ premises_str ^
    "\tDiagrammes de la combinaison :\n" ^ string_of_diagrams_list comb ^
    "\tDiagrammes de la conclusion :\n" ^ string_of_diagrams_list str_dc ^
    "\tConclusion " ^
    (if est_compatible_premisses_conc ps c then "compatible"
    else "incompatible avec les diagrammes, contre-exemples :\n" ^
        string_of_diagrams_list (List.map string_of_diag (temoins_incompatibilite_premisses_conc ps c)))
  in
    print_string s
    