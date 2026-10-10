import Holant.Certificates.OctahedralSeparator.PreparedData

namespace Holant.Certificates.OctahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

def rowIndex (f : Form) (r : Fin 15) : Fin 48 :=
  Fin.ofNat 48 ((if f=0 then 0 else if f=1 then 9 else if f=2 then 18 else 33)+r.val)

theorem rowIndex_correct : ∀ f : Form, ∀ r : Fin 15, admissible f r →
    rowForm (rowIndex f r)=f ∧ rowBase (rowIndex f r)=r := by decide

def regularRow (f : Form) (r : Fin 9) : Fin 48 := rowIndex f (Fin.castAdd 6 r)
def mixedForm (f : Fin 2) : Form := Fin.natAdd 2 f
def deficientRow (f : Fin 2) (p : Fin 6) : Fin 48 := rowIndex (mixedForm f) (Fin.natAdd 9 p)

theorem regularRow_form (f : Form) (r : Fin 9) : rowForm (regularRow f r)=f := by
  exact (rowIndex_correct _ _ (Or.inl r.isLt)).1
theorem regularRow_base (f : Form) (r : Fin 9) : rowBase (regularRow f r)=Fin.castAdd 6 r := by
  exact (rowIndex_correct _ _ (Or.inl r.isLt)).2
theorem deficientRow_form (f : Fin 2) (p : Fin 6) : rowForm (deficientRow f p)=mixedForm f := by
  exact (rowIndex_correct _ _ (Or.inr (by simp [mixedForm]))).1
theorem deficientRow_base (f : Fin 2) (p : Fin 6) : rowBase (deficientRow f p)=Fin.natAdd 9 p := by
  exact (rowIndex_correct _ _ (Or.inr (by simp [mixedForm]))).2

/-- Every ordering, not only a list of supplied permutations. -/
theorem permutations_complete : ∀ τ : Fin 3 → Fin 3,
    Function.Bijective τ ↔ ∃ p : Fin 6, τ=permutations p := by decide

theorem permutations_distinct : Function.Injective permutations := by decide

end Holant.Certificates.OctahedralSeparator
