package leo.modules.output.LPoutput

import leo.modules.output.LPoutput.lpDatastructures._

object LPSignature {

  abstract class lpAxioms extends lpTerm{
    def name: lpConstantTerm
    def ty: lpMlType
  }

  case object lpEm extends lpAxioms{
    //  Π x: Prop, Prf (x ∨ ¬ x)
    override def name: lpConstantTerm = lpConstantTerm("em")
    override def ty: lpMlType = lpMlDependType(Seq(lpTypedVar(lpConstantTerm("x"),lpOtype.lift2Meta)),lpOlUntypedBinaryConnectiveTerm(lpOr,lpOlConstantTerm("x"),lpOlUnaryConnectiveTerm(lpNot,lpOlConstantTerm("x"))).prf)
    override def pretty: String = lpDeclaration(lpEm.name,Seq.empty,lpEm.ty).pretty
  }

  abstract class lpTheorems extends lpTerm {
    def name: lpConstantTerm
    override def pretty: String = name.pretty
  }

  object lpTheorems {
    case object eqImp extends lpTheorems {
      override def name: lpConstantTerm = lpConstantTerm("=⇒")
    }
  }

  case object lpDne extends lpAxioms {
    // symbol dne x : π(¬ ¬ x) → π x
    // todo: add proof encoding
    override def name: lpConstantTerm = lpConstantTerm("¬¬ₑ")

    override def ty: lpMlType = lpMlDependType(Seq(lpTypedVar(lpConstantTerm("x"), lpOtype.lift2Meta)),lpMlFunctionType(Seq(lpOlUnaryConnectiveTerm(lpNot,lpOlUnaryConnectiveTerm(lpNot,lpOlConstantTerm("x"))).prf,lpOlConstantTerm("x").prf)))

    override def pretty: String = lpDeclaration(lpDne.name, Seq.empty, lpDne.ty).pretty
  }

  case object lpPropExt extends lpAxioms {
    override def name: lpConstantTerm = lpConstantTerm("propExt")

    // Π x: Els (↑ o), Π y: Els (↑ o), (Prf x → Prf y) → (Prf y → Prf x) → Prf (eq x y)
    override def ty: lpMlType = lpMlDependType(Seq(lpTypedVar(lpConstantTerm("x"), lpOtype.lift2Meta),lpTypedVar(lpConstantTerm("y"), lpOtype.lift2Meta)), lpMlFunctionType(Seq(lpMlFunctionType(Seq(lpOlConstantTerm("x").prf,lpOlConstantTerm("y").prf)),lpMlFunctionType(Seq(lpOlConstantTerm("y").prf,lpOlConstantTerm("x").prf)),lpOlTypedBinaryConnectiveTerm(lpEq,lpOtype,lpOlConstantTerm("x"),lpOlConstantTerm("y")).prf)))

    override def pretty: String = lpDeclaration(lpPropExt.name, Seq.empty, lpPropExt.ty).pretty
  }

  val tempLib: String = "require open Stdlib.Set Stdlib.Prop Stdlib.PropExt Stdlib.List;\n\n/******************************************************************************\n *  Setup for the user defined tactic         \n ******************************************************************************/\n\n constant symbol Tactic : TYPE;\n symbol tactic : Set;\n rule τ tactic ↪ Tactic;\n\n constant symbol String : TYPE;\n builtin \"String\" ≔ String;\n \n symbol #rewrite : String → String → Π [a], π a → Tactic;\n builtin \"rewrite\" ≔ #rewrite;\n \n symbol #orelse : Tactic → Tactic → Tactic;\n builtin \"orelse\" ≔ #orelse;\n notation #orelse infix left 10000;\n \n symbol #refine : String → Tactic;\n builtin \"refine\" ≔ #refine;\n \n symbol #repeat : Tactic → Tactic;\n builtin \"repeat\" ≔ #repeat;\n \n symbol #fail : Tactic;\n builtin \"fail\" ≔ #fail;\n \n symbol #admit : Tactic;\n builtin \"admit\" ≔ #admit;\n \n symbol #and : Tactic → Tactic → Tactic;\n builtin \"and\" ≔ #and;\n \n symbol #apply : Π [a], π a → Tactic;\n builtin \"apply\" ≔ #apply;\n \n symbol #assume : String → Tactic;\n builtin \"assume\" ≔ #assume;\n \n symbol #generalize : Π [a], π a → Tactic;\n builtin \"generalize\" ≔ #generalize;\n \n symbol #have : String → Π [a], π a → Tactic;\n builtin \"have\" ≔ #have; \n \n symbol #induction : Tactic;\n builtin \"induction\" ≔ #induction; \n \n symbol #remove : Π [a], π a → Tactic;\n builtin \"remove\" ≔ #remove;\n \n symbol #reflexivity : Tactic;\n builtin \"reflexivity\" ≔ #reflexivity;\n \n symbol #set : String → Π [a], π a → Tactic;\n builtin \"set\" ≔ #set;\n \n symbol #simplify : Tactic;\n builtin \"simplify\" ≔ #simplify;\n\n symbol #simplify_beta : Tactic;\n builtin \"simplify rule off\" ≔ #simplify_beta;\n \n symbol #solve : Tactic;\n builtin \"solve\" ≔ #solve;\n \n symbol #symmetry : Tactic;\n builtin \"symmetry\" ≔ #symmetry;\n \n symbol #try : Tactic;\n builtin \"try\" ≔ #try;\n \n symbol #why3 : Tactic;\n builtin \"why3\" ≔ #why3; \n\n \n // necessary in order to define the tactics\n protected symbol set0 : Set;\n rule τ set0 ↪ Set;\n \n \n/******************************************************************************\n*  Definition of Leo-III simplification tactic        \n******************************************************************************/\n \n symbol applyAny : \uD835\uDD43 tactic → Tactic;\n rule applyAny ($t0 ⸬ $tl) ↪ $t0 #orelse (applyAny $tl)\n with applyAny □ ↪ #fail;\n \n symbol listOfAllSimpRules ≔ ((#rewrite \"\" \"\" ∨_idem) ⸬ (#rewrite \"\" \"\" em_eq_l) ⸬ (#rewrite \"\" \"\" em_eq_r) ⸬ (#rewrite \"\" \"\" ∨⊤) ⸬ \n     (#rewrite \"\" \"\" ⊤∨) ⸬ (#rewrite \"\" \"\" ∨⊥) ⸬ (#rewrite \"\" \"\" ⊥∨) ⸬ (#rewrite \"\" \"\" ∧_idem) ⸬ (#rewrite \"\" \"\" ∧_contra_r) ⸬ (#rewrite \"\" \"\" ∧_contra_l) ⸬ \n     (#rewrite \"\" \"\" ∧⊤) ⸬ (#rewrite \"\" \"\" ⊤∧) ⸬ (#rewrite \"\" \"\" ∧⊥) ⸬ (#rewrite \"\" \"\" ⊥∧) ⸬ (#rewrite \"\" \"\" ⇒⊤) ⸬ (#rewrite \"\" \"\" ⊥⇒) ⸬ (#rewrite \"\" \"\" ⊤⇒) ⸬ \n     (#rewrite \"\" \"\" ⇒⊥) ⸬ (#rewrite \"\" \"\" ⇒_idem) ⸬ (#rewrite \"\" \"\" ⇔⊤) ⸬ (#rewrite \"\" \"\" ⊤⇔) ⸬ (#rewrite \"\" \"\" ⊥⇔) ⸬ (#rewrite \"\" \"\" ⇔⊥) ⸬ \n     (#rewrite \"\" \"\" ⇔_idem) ⸬ (#rewrite \"\" \"\" ¬⊤) ⸬ (#rewrite \"\" \"\" ¬⊥) ⸬ (#rewrite \"\" \"\" ¬¬ₑ_eq) ⸬ (#rewrite \"\" \"\" =⊤) ⸬ (#rewrite \"\" \"\" ⊤=) ⸬ \n     (#rewrite \"\" \"\" =⊥) ⸬ (#rewrite \"\" \"\" ⊥=) ⸬ (#rewrite \"\" \"\" =_idem) ⸬ (#rewrite \"\" \"\" ¬=⊥) ⸬ (#rewrite \"\" \"\" ¬⊥=) ⸬ (#rewrite \"\" \"\" ¬=⊤) ⸬ \n     (#rewrite \"\" \"\" ¬⊤=) ⸬ (#rewrite \"\" \"\" ¬=_idem) ⸬ (#rewrite \"\" \"\" ∀_const) ⸬ (#rewrite \"\" \"\" ∃_const) ⸬ (#rewrite \"\" \"\" polarity_switch) ⸬ (#refine \"⊤ᵢ\") ⸬ □);\n \n symbol applyAllSimplifications ≔ #repeat (applyAny listOfAllSimpRules);\n\n\n/******************************************************************************\n*  Definition of Leo-III clausification tactic        \n******************************************************************************/\n\nsymbol normAsso ≔ #repeat ((#rewrite \"\" \"\" ∧_assoc) #orelse (#rewrite \"\" \"\" ∨_assoc));\n\nsymbol allCNFids_list ≔ ((#rewrite \"\" \"\" deMorgan_∧) ⸬ (#rewrite \"\" \"\" deMorgan_∨) ⸬ (#rewrite \"\" \"\" ⇒=∨) ⸬ (#rewrite \"\" \"\" ¬⇒=∧¬) ⸬ (#and (#rewrite \"\" \"\" ∧∨_dist_l) normAsso) ⸬ (#and (#rewrite \"\" \"\" ∧∨_dist_r) normAsso) ⸬ (#rewrite \"\" \"\" ¬¬ₑ_eq) ⸬ □);\n\nsymbol allCNFids_app ≔ #and (#and (#repeat (applyAny allCNFids_list)) normAsso) #reflexivity;"

}
