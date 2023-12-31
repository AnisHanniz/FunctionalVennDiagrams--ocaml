(** Type des formules de la logique propositionnelle *)
type formule_log_prop =
  | Bot
  | Top
  | Atome of string
  | Et of formule_log_prop * formule_log_prop
  | Ou of formule_log_prop * formule_log_prop
  | Imp of formule_log_prop * formule_log_prop
  | Non of formule_log_prop
  | Xor of formule_log_prop * formule_log_prop
  | Equiv of formule_log_prop * formule_log_prop
  | Aucun of formule_log_prop list
  | Tous of formule_log_prop list
  | AuMoins of int * formule_log_prop list
  | AuPlus of int * formule_log_prop list

(** atome_dans_f f : renvoie une string list correspondant à la liste de tous
    les atomes de f*)
let rec atome_dans_f (f : formule_log_prop) : string list =
  match f with 
  | Bot -> []
  | Top -> []
  | Atome s -> [s]
  | Et (f1, f2) -> atome_dans_f f1 @ atome_dans_f f2
  | Ou (f1, f2) -> atome_dans_f f1 @ atome_dans_f f2
  | Imp (f1, f2) -> atome_dans_f f1 @ atome_dans_f f2
  | Non f1 -> atome_dans_f f1
  | Xor (f1, f2) -> atome_dans_f f1 @ atome_dans_f f2
  | Equiv (f1, f2) -> atome_dans_f f1 @ atome_dans_f f2
  | Aucun lf -> List.flatten (List.map atome_dans_f lf)
  | Tous lf -> List.flatten (List.map atome_dans_f lf)
  | AuMoins (_, lf) -> List.flatten (List.map atome_dans_f lf)
  | AuPlus (_, lf) -> List.flatten (List.map atome_dans_f lf)

(** AF est_dans_liste l str : renvoie vrai si le string str est un élément de la string 
    list l *)
let est_dans_liste (l : string list) (str : string) = List.mem str l

(** AF fusion_liste l1 l2 : rajoute dans l2 tous les éléments de l1 s'ils ne sont
    pas déjà dans l2*)
let fusion_liste (l1 : string list) (l2 : string list) : string list =
  l1 @ List.filter (fun e -> not (est_dans_liste l1 e)) l2

(** AF eval_Formule_Log_Prop list f : renvoie vrai si f est vrai selon
    l'interprétation list caractérisée par une string list*)
let rec eval_Formule_Log_Prop (list: string list) (f: formule_log_prop) : bool =
  match f with 
  | Bot -> false 
  | Top -> true 
  | Atome s -> est_dans_liste list s
  | Non f1 -> not (eval_Formule_Log_Prop list f1)
  | Et(f1, f2) -> eval_Formule_Log_Prop list f1 && eval_Formule_Log_Prop list f2 
  | Ou(f1, f2) -> eval_Formule_Log_Prop list f1 || eval_Formule_Log_Prop list f2
  | Imp(f1, f2) -> not (eval_Formule_Log_Prop list f1) || eval_Formule_Log_Prop list f2
  | Xor(f1, f2) -> let p = eval_Formule_Log_Prop list f1 in 
                   let q = eval_Formule_Log_Prop list f2 in 
                   (p || q) && not (p && q)
  | Equiv(f1, f2) -> eval_Formule_Log_Prop list f1 = eval_Formule_Log_Prop list f2
  | Aucun lf -> List.for_all (fun f -> not (eval_Formule_Log_Prop list f)) lf
  | Tous lf -> List.for_all (fun f -> eval_Formule_Log_Prop list f) lf
  | AuMoins (n, lf) -> 
    List.length (List.filter (fun f -> eval_Formule_Log_Prop list f) lf) >= n
  | AuPlus (n, lf) -> 
    List.length (List.filter (fun f -> eval_Formule_Log_Prop list f) lf) <= n



(** AF table_verite alpha f : renvoie la table de vérité de f sur les atomes issus 
    de f ou de alpha *)
let table_verite (alpha : string list) (f : formule_log_prop) :
    (string list * bool) list =
    let rec aux alpha f acc r =
      match alpha with 
      | [] -> (acc, eval_Formule_Log_Prop acc f) :: r
      | t::q -> aux q f (t::acc) r @ aux q f (acc) r
    in aux (List.rev (fusion_liste (atome_dans_f f) alpha)) f [] []

(** AF string_of_formule_log_prop_var str f : conversion d'une formule f en chaîne 
    de caractères, en les représentant comme des prédicats unaires appliqués sur
    des occurrences de la variable str. *)
let rec string_of_formule_log_prop_var (str : string) (f : formule_log_prop) : string
    =
    match f with 
    | Bot -> "⊥"
    | Top -> "⊤"
    | Atome s1 -> s1 ^ "(" ^ str ^ ")"
    | Non f1 -> "¬" ^ string_of_formule_log_prop_var str f1
    | Et(f1, f2) -> "(" ^ string_of_formule_log_prop_var str f1 ^ " ∧ " ^ 
                    string_of_formule_log_prop_var str f2 ^ ")" 
    | Ou(f1, f2) -> "(" ^ string_of_formule_log_prop_var str f1 ^ " ∨ " ^
                    string_of_formule_log_prop_var str f2 ^ ")"
    | Imp(f1, f2) -> "(" ^ string_of_formule_log_prop_var str f1 ^ " → " ^
                     string_of_formule_log_prop_var str f2 ^ ")"
    | Xor(f1, f2) -> "(" ^ string_of_formule_log_prop_var str f1 ^ " ⊕ " ^
                      string_of_formule_log_prop_var str f2 ^ ")"
    | Equiv(f1, f2) -> "(" ^ string_of_formule_log_prop_var str f1 ^ " ↔ " ^
                       string_of_formule_log_prop_var str f2 ^ ")"
    | Aucun lf -> "Aucun(" ^ string_of_formule_log_prop_var str (List.hd lf) ^ ")"
    | Tous lf -> "Tous(" ^ string_of_formule_log_prop_var str (List.hd lf) ^ ")"
    | AuMoins (n, lf) -> "AuMoins(" ^ string_of_int n ^ ", " ^
                         string_of_formule_log_prop_var str (List.hd lf) ^ ")"
    | AuPlus (n, lf) -> "AuPlus(" ^ string_of_int n ^ ", " ^
                        string_of_formule_log_prop_var str (List.hd lf) ^ ")"

