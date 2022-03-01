(*****************************************)
(*  Project: While Language              *)
(*  Author: Cristiano Di Bari            *)
(*  Course: Foundations of Languages     *)
(*****************************************)

load "Int";
load "Bool";
load "Listsort";
load "Random";

(*****************************************)
(*  SYNTAX                               *)
(*****************************************)

(* Locations *)
type loc = string

(* Operations *)
datatype oper = Add | Geq

(* Expressions *)
datatype expr = Integer of int
              | Boolean of bool
              | Op      of expr * oper * expr
              | If      of expr * expr * expr
              | Seq     of expr * expr
              | While   of expr * expr
              | Assign  of loc  * expr
              | Deref   of loc
              | Par     of expr * expr
              | Choice  of expr * expr
              | Await   of expr * expr
              | Skip

(* Types of expressions *)
datatype Texp = int | bool | unit | proc

(* Types of locations *)
datatype Tloc = intref



(*****************************************)
(*  STORE                                *)
(*****************************************)

(* Type of store *)
type store = (loc * int) list

(* Gets the value of a store location *)
fun lookup ([], l) = NONE
  | lookup ((l', n)::store, l) = 
      if l = l' then SOME n
      else lookup (store, l)

(* Iterates the store to find the pair to update *)
fun update_iterator front [] (l, n) = NONE
  | update_iterator front ((l', n')::tail) (l, n) =
        if l' = l then SOME (front @ (l, n)::tail)
        else update_iterator ((l', n')::front) tail (l, n)

(* Updates a store location *)
fun update (s, (l, n)) = update_iterator [] s (l, n)



(*****************************************)
(*  INTERPRETER                          *)
(*****************************************)

(* Random generator *)
val rndGen = Random.newgen()

(* Checks if an expression is a value *)
fun value (Integer n)     = true
  | value (Boolean b)     = true
  | value (Skip)          = true
  | value _               = false


(* Performs a single computation step *)
fun reduce (Integer n, s)     = NONE                                          
  | reduce (Boolean b, s)     = NONE
  | reduce (Skip, s)          = NONE

  | reduce (Op (e1, oper, e2), s) = (
      case (e1, oper, e2) of
          (Integer n1, Add, Integer n2) => SOME (Integer (n1 + n2), s)      (* op + *)
        | (Integer n1, Geq, Integer n2) => SOME (Boolean (n1 >= n2), s)     (* op >= *)
        | (e1, oper, e2) => (
            if value e1 then
              case reduce (e2, s) of
                  SOME (e2', s') => SOME (Op (e1, oper, e2'), s')           (* op2 *)
                | NONE => NONE
            else
              case reduce (e1, s) of
                  SOME (e1', s') => SOME (Op (e1', oper, e2), s')           (* op1 *)
                | NONE => NONE
          )  
    )

  | reduce (If (e1, e2, e3), s) = (
      case e1 of
          Boolean true  => SOME (e2, s)                                     (* if-tt *)
        | Boolean false => SOME (e3, s)                                     (* if-ff *)  
        | _ => (
            case reduce (e1, s) of
                SOME (e1', s') => SOME (If (e1', e2, e3), s')               (* if *)
              | NONE => NONE
          )
    )

  | reduce (Seq (e1, e2), s) = (
      case e1 of
          Skip => SOME (e2, s)                                              (* seq-skip *)
        | _ => (
            case reduce (e1, s) of
                SOME (e1', s') => SOME (Seq (e1', e2), s')                  (* seq *)
              | NONE => NONE
          )
    )

  | reduce (While (e1, e2), s) = (
      SOME (If (e1, Seq (e2, While (e1, e2)), Skip), s)                     (* while *)
    )

  | reduce (Assign (l, e), s) = (
      case e of
          Integer n => (
            case update (s, (l, n)) of
                SOME s' => SOME (Skip, s')                                  (* assign1 *)
              | NONE => NONE
          )
        | _ => (
            case reduce (e, s) of
                SOME (e', s') => SOME (Assign (l, e'), s')                  (* assign2 *)
              | NONE => NONE
          )
    )

  | reduce (Deref l, s) = (
      case lookup (s, l) of
          SOME n => SOME (Integer n, s)                                     (* deref *)
        | NONE => NONE
    )

  | reduce (Par (e1, e2), s) = (
      case Random.range(0,2) rndGen of
          0 => (
            case e1 of
                Skip => SOME (e2, s)                                        (* end-L *)
              | _ => (
                  case reduce (e1, s) of
                      SOME (e1', s') => SOME (Par (e1', e2), s')            (* par-L *)
                    | NONE => NONE
                )
          )
        | 1 => (
            case e2 of
                Skip => SOME (e1, s)                                        (* end-R *)
              | _ => (
                  case reduce (e2, s) of
                      SOME (e2', s') => SOME (Par (e1, e2'), s')            (* par-R *)
                    | NONE => NONE
                )
        )
    )

  | reduce (Choice (e1, e2), s) = (
      case Random.range(0,2) rndGen of
          0 => (
            case reduce (e1, s) of
                SOME (e1', s') => SOME (e1', s')                            (* choice-L *)
              | NONE => NONE
          )
        | 1 => (
            case reduce (e2, s) of
                SOME (e2', s') => SOME (e2', s')                            (* choice-R *)
              | NONE => NONE
          )
    )

  | reduce (Await (e1, e2), s) = (
      let fun eval (e, s) = 
            case reduce (e, s) of
                NONE => (e, s)
              | SOME (e', s') => eval (e', s')
      in
        case eval (e1, s) of
            (Boolean true, s') => (
              case eval (e2, s') of
                  (Skip, s'') => SOME (Skip, s'')                           (* await *)
                | _ => NONE
            )
          | (Boolean false, s') => SOME (Await (e1, e2), s)
          | _ => NONE
      end
    )


(* Evaluate expression 'e' relative to store 's' *)
fun evaluate (e, s) = 
    case reduce (e, s) of
        NONE => (e, s)
      | SOME (e', s') => evaluate (e', s')



(*****************************************)
(*  TYPE CHECKER                         *)
(*****************************************)

(* Evaluate the type of expression 'e' in type environment 'gamma' *)
fun inferType gamma (Integer n) = SOME int                                      (* int *)
  | inferType gamma (Boolean b) = SOME bool                                     (* bool *)
  | inferType gamma (Skip)      = SOME unit                                     (* skip *)

  | inferType gamma (Op (e1, oper, e2)) = (
      case (inferType gamma e1, oper, inferType gamma e2) of
          (SOME int, Add, SOME int) => SOME int                                 (* op + *)
        | (SOME int, Geq, SOME int) => SOME bool                                (* op >= *)
        | _ => NONE
    )

  | inferType gamma (If (e1, e2, e3)) = (
      case (inferType gamma e1, inferType gamma e2, inferType gamma e2) of
          (SOME bool, SOME t1, SOME t2) => if t1 = t2 then SOME t1 else NONE    (* if *)
        | _ => NONE
    )

  | inferType gamma (Seq (e1, e2)) = (
      case (inferType gamma e1, inferType gamma e2) of
          (SOME unit, SOME t) => SOME t                                         (* seq *)
        | _ => NONE
    )

  | inferType gamma (While (e1, e2)) = (
      case (inferType gamma e1, inferType gamma e2) of
          (SOME bool, SOME unit) => SOME unit                                   (* while *)
        | _ => NONE
    )

  | inferType gamma (Assign (l, e)) = (
      case (lookup (gamma, l), inferType gamma e) of
          (SOME intref, SOME int) => SOME unit                                  (* assign *)
        | _ => NONE
    )

  | inferType gamma (Deref (l)) = (
      case lookup (gamma, l) of                                                 
          SOME intref => SOME int                                               (* deref *)
        | _ => NONE
    )

  | inferType gamma (Par (e1, e2)) = (
      case (inferType gamma e1, inferType gamma e2) of
          (SOME unit, SOME unit) => SOME proc                                   (* par *)
        | (SOME unit, SOME proc) => SOME proc
        | (SOME proc, SOME unit) => SOME proc
        | (SOME proc, SOME proc) => SOME proc
        | _ => NONE 
    )

  | inferType gamma (Choice (e1, e2)) = (
      case (inferType gamma e1, inferType gamma e2) of
          (SOME unit, SOME unit) => SOME unit                                   (* choice *)
        | _ => NONE
    )

  | inferType gamma (Await (e1, e2)) = (
      case (inferType gamma e1, inferType gamma e2) of
          (SOME bool, SOME unit) => SOME unit                                   (* await *)
        | _ => NONE
    )



(*****************************************)
(*  PRETTY PRINTER                       *)
(*****************************************)

fun printOper Add   = "+"
  | printOper Geq   = ">="


fun printType (int)   = "int"
  | printType (bool)  = "bool"
  | printType (unit)  = "unit"
  | printType (proc)  = "proc"


fun printExpr (Integer n)           = (Int.toString n)
  | printExpr (Boolean b)           = (Bool.toString b)
  | printExpr (Op (e1, oper, e2))   = "(" ^ (printExpr e1) ^ " " ^ (printOper oper) ^ " " ^ (printExpr e2) ^ ")"
  | printExpr (If (e1, e2, e3))     = "if " ^  (printExpr e1) ^ " then " ^ (printExpr e2) ^ " else " ^ (printExpr e3)
  | printExpr (Seq (e1, e2))        = (printExpr e1) ^ ";" ^ (printExpr e2)
  | printExpr (While (e1, e2))      = "while " ^ (printExpr e1) ^ " do " ^ (printExpr e2)
  | printExpr (Assign (l, e))       = l ^ " := " ^ (printExpr e)
  | printExpr (Deref l)             = "!" ^ l
  | printExpr (Par (e1, e2))        = "(" ^ (printExpr e1) ^ ")" ^ " || " ^ "(" ^ (printExpr e2) ^ ")"
  | printExpr (Choice (e1, e2))     = "(" ^ (printExpr e1) ^ ")" ^ " (+) " ^ "(" ^ (printExpr e2) ^ ")"
  | printExpr (Await (e1, e2))      = "await (" ^ (printExpr e1) ^ ") protect (" ^ (printExpr e2) ^ ")" ^ " end"
  | printExpr (Skip)                = "skip"


fun printLocations [] = ""
  | printLocations ((l, n)::tail) = l ^ "->" ^ (Int.toString n) ^ " " ^ (printLocations tail)


fun printStore s = 
  let val s' = Listsort.sort (fn ((l, n), (l', n')) => String.compare (l, l')) s
  in "{" ^ printLocations s' ^ "}" 
  end


(* Print configuration < e, s > *)
fun printConfig (e, s) = "< " ^ (printExpr e) ^ " , " ^ (printStore s) ^ " >"


fun printEval (e, s) = (
  print (("\n --> ") ^ printConfig (e, s));
  case reduce (e, s) of
      SOME (e', s') => printEval (e', s')
    | NONE => (
        print ("\n -/->  ");
        if value e then
          print ("Evaluation: " ^ printExpr (e) ^ "\n\n")
        else
          print ("Stuck: not a value!\n\n")
      )
)
