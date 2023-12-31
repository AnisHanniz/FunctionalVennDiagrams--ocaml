open Formule_Log_Prop

(** Type des formules utilisées pour les syllogismes *)
type formule_syllogisme =
  | PourTout of formule_log_prop
  | IlExiste of formule_log_prop

(** AF string_of_formule f : conversion d'une formule f en chaîne de caractères,
    en considérant des prédicats unaires appliqués sur des 
    occurrences de la variable s. *)
    let string_of_formule (f : formule_syllogisme) : string =
      let var_name = "x" in
      let formule_string = string_of_formule_log_prop_var var_name in
      match f with
      | PourTout formule -> "∀( " ^ formule_string formule ^ " )"
      | IlExiste formule -> "∃( " ^ formule_string formule ^ " )"