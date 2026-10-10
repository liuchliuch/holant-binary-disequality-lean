import Holant.Complexity.UniversalPairReduction.BinaryFamily
import Holant.Complexity.UniversalPairReduction.QuerySemantics
import Holant.Complexity.UniversalPairReduction.Surgery.Denotation
import Holant.Complexity.FixedGadgetSubstitution.OriginalFamily

/-! The two actual fixed-gadget query values are the original input interpreted
with the distinguished label replaced by B and B transpose, respectively. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.Complexity.UniversalPairReduction.QueryFamily
open Holant.Algebraic FixedGadgetSubstitution
variable {K : Type} [Field K] [Algebra ℚ K] {s : ℕ} {arity : ℕ → ℕ} {S : NetworkShape 2}
variable (G : (i : Fin s) → Signature K (arity i.val)) (L : Labelling S s 1 arity)

def coeff : ExactSignatureTables.CoefficientIndex s 1 arity → K
  | .inl ⟨i,x⟩ => G i x
  | .inr (_,a,b) => Signature.disequality a b

def binary (p : Equiv.Perm (Fin 2)) : BinaryTable K := fun a b =>
  ((permuteLabelling L p).sourceNetwork G (fun _ : Fin 1 => Signature.disequality)).denote ![a,b]

 theorem old_heq (p : Equiv.Perm (Fin 2)) (i : Fin s) :
    HEq (OrderedQueries.sourceSignatures L p G (fun _ : Fin 1 => Signature.disequality) (Fin.castAdd 1 i))
      (G i) :=
  OriginalFamily.ambientSource_old (coeff G) (permuteLabelling L p).template
    (permuteLabelling L p).wellFormed i

 theorem new_heq (p : Equiv.Perm (Fin 2)) :
    HEq (OrderedQueries.sourceSignatures L p G (fun _ : Fin 1 => Signature.disequality) ⟨s,by omega⟩)
      ((permuteLabelling L p).sourceNetwork G (fun _ : Fin 1 => Signature.disequality)).denote := by
  have hh := OriginalFamily.ambientSource_new (coeff G) (permuteLabelling L p).template
    (permuteLabelling L p).wellFormed
  have ht := Labelling.denote_template (permuteLabelling L p) G (fun _ : Fin 1 => Signature.disequality)
  exact hh.trans (heq_of_eq ht)

private theorem list_apply_heq {m n : ℕ} {f : Signature K m} {g : Signature K n}
    (hm : m=n) (he : HEq f g) (bits : List Bool) :
    f (fun i => bits.getD i.val false)=g (fun i => bits.getD i.val false) := by
  subst n
  cases eq_of_heq he
  rfl

 theorem table_eq (p : Equiv.Perm (Fin 2)) :
    Surgery.Choice.table (OrderedQueries.sourceSignatures L p G (fun _ : Fin 1 => Signature.disequality)) =
      Surgery.Choice.table (BinaryFamily.signatures G (binary G L p)) := by
  funext i bits
  by_cases hi : i<s+1
  · by_cases hold : i<s
    · rw [BinaryFamily.table_old G _ i hold]
      unfold Surgery.Choice.table
      rw [dif_pos hi,dif_pos hold]
      exact list_apply_heq (by rw [OrderedQueries.arity_eq]; simp [extendedArity,hold])
        (old_heq G L p ⟨i,hold⟩) bits
    · have hie : i=s := by omega
      subst i
      rw [BinaryFamily.table_new]
      unfold Surgery.Choice.table
      rw [dif_pos (Nat.lt_succ_self s)]
      calc
        _ = ((permuteLabelling L p).sourceNetwork G (fun _ : Fin 1 => Signature.disequality)).denote
            (fun i => bits.getD i.val false) := list_apply_heq (by rw [OrderedQueries.arity_eq]; simp [extendedArity])
          (new_heq G L p) bits
        _ = _ := by
          unfold binary
          congr 1
          funext i
          fin_cases i <;> rfl
  · simp [Surgery.Choice.table,hi]

 theorem query_value (p : Equiv.Perm (Fin 2)) (r : Input s arity) :
    Surgery.targetValue G (OrderedQueries.query L p (forget s arity r)) =
      BinaryFamily.value G (binary G L p) r := by
  unfold Surgery.targetValue
  rw [OrderedQueries.query_value]
  unfold OrderedQueries.sourceValue
  rw [Surgery.Choice.denote_eq_evaluate,table_eq]
  exact (BinaryFamily.value_evaluate G _ r).symm

 theorem binary_plus : binary G L (Equiv.refl _)=fun a b =>
    (L.sourceNetwork G (fun _ : Fin 1 => Signature.disequality)).denote ![a,b] := by
  funext a b
  exact denote_permute L G (fun _ : Fin 1 => Signature.disequality) (Equiv.refl _) ![a,b]

 theorem binary_minus : binary G L (Equiv.swap 0 1)=(binary G L (Equiv.refl _)).transpose := by
  funext a b
  rw [binary,denote_permute,binary_plus]
  change _=(L.sourceNetwork G (fun _ : Fin 1 => Signature.disequality)).denote ![b,a]
  congr 1
  funext i
  fin_cases i <;> simp

end Holant.Complexity.UniversalPairReduction.QueryFamily
