import Holant.Tractable.Criteria
import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionTensor

/-! Phase twists commute with ordered tensor products, and either EO class
reflects to each nonzero factor. These are semantic restriction statements;
they declare no extra physical pins or signatures available. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseWholeFamily
open Holant Holant.Tractable
namespace X
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor
  (tensor tensor_nonzero affine_left affine_right product_left product_right)
end X
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option maxRecDepth 16384
set_option Elab.async false

/-- A common diagonal phase in the original ordered coordinates. -/
def twist {n : ℕ} (r : AlgebraicComplex) (f : Signature AlgebraicComplex n) :
    Signature AlgebraicComplex n:=fun z=>r^(weight z)*f z

theorem twist_zero (r : AlgebraicComplex) (n : ℕ) :
    twist r (0 : Signature AlgebraicComplex n)=0 := by
  funext z
  simp [twist]

theorem twist_nonzero {n : ℕ} {r : AlgebraicComplex} (hr : r≠0)
    {f : Signature AlgebraicComplex n} (hf : f≠0) : twist r f≠0 := by
  obtain ⟨z,hz⟩:=Function.ne_iff.mp hf
  intro zero
  have he:=congrFun zero z
  exact mul_ne_zero (pow_ne_zero _ hr) hz he

theorem weight_split {m n : ℕ} (z : Fin (m+n)→Bool) :
    weight z=weight (fun i=>z (Fin.castAdd n i))+weight (fun i=>z (Fin.natAdd m i)) := by
  simp only [weight,Fin.sum_univ_add]

theorem twist_tensor {m n : ℕ} (r : AlgebraicComplex)
    (f : Signature AlgebraicComplex m) (g : Signature AlgebraicComplex n) :
    twist r (X.tensor f g)=X.tensor (twist r f) (twist r g) := by
  funext z
  change r^(weight z)*(f (fun i=>z (Fin.castAdd n i))*g (fun i=>z (Fin.natAdd m i)))=
    (r^(weight (fun i=>z (Fin.castAdd n i)))*f (fun i=>z (Fin.castAdd n i)))*
    (r^(weight (fun i=>z (Fin.natAdd m i)))*g (fun i=>z (Fin.natAdd m i)))
  rw [weight_split,pow_add]
  ring

theorem class_zero (C : EOClass) (n : ℕ) : C.Holds (0 : Signature AlgebraicComplex n) := by
  cases C
  · exact affine_zero n
  · exact product_zero n

theorem class_left (C : EOClass) {m n : ℕ}
    {f : Signature AlgebraicComplex m} {g : Signature AlgebraicComplex n} (ng : g≠0)
    (good : C.Holds (X.tensor f g)) : C.Holds f := by
  cases C
  · exact X.affine_left finSumFinEquiv ng good
  · exact X.product_left finSumFinEquiv ng good

theorem class_right (C : EOClass) {m n : ℕ}
    {f : Signature AlgebraicComplex m} {g : Signature AlgebraicComplex n} (nf : f≠0)
    (good : C.Holds (X.tensor f g)) : C.Holds g := by
  cases C
  · exact X.affine_right finSumFinEquiv nf good
  · exact X.product_right finSumFinEquiv nf good

/-- Ordered semantic list tensor, also retaining nonzero nullary scalars. -/
def listArity : List (AnySignature AlgebraicComplex)→ℕ
  | []=>0
  | f::fs=>f.1+listArity fs

def listValue : (fs : List (AnySignature AlgebraicComplex))→Signature AlgebraicComplex (listArity fs)
  | []=>fun _=>1
  | f::fs=>X.tensor f.2 (listValue fs)

theorem list_nonzero (fs : List (AnySignature AlgebraicComplex))
    (nonzero : ∀f∈fs,f.2≠0) : listValue fs≠0 := by
  induction fs with
  | nil=>
      intro h
      exact one_ne_zero (congrFun h Fin.elim0)
  | cons f fs ih=>
      exact X.tensor_nonzero (nonzero f List.mem_cons_self)
        (ih (fun g hg=>nonzero g (List.mem_cons_of_mem f hg)))

theorem list_classes (C : EOClass) (r : AlgebraicComplex) (hr : r≠0)
    (fs : List (AnySignature AlgebraicComplex)) (nonzero : ∀f∈fs,f.2≠0)
    (good : C.Holds (twist r (listValue fs))) : ∀f∈fs,C.Holds (twist r f.2) := by
  induction fs with
  | nil=>simp
  | cons f fs ih=>
      change C.Holds (twist r (X.tensor f.2 (listValue fs))) at good
      rw [twist_tensor] at good
      have tailnz:=list_nonzero fs (fun g hg=>nonzero g (List.mem_cons_of_mem f hg))
      have headnz:=nonzero f List.mem_cons_self
      intro g hg
      rcases List.mem_cons.mp hg with rfl|hg
      · exact class_left C (twist_nonzero hr tailnz) good
      · exact ih (fun h hh=>nonzero h (List.mem_cons_of_mem f hh))
          (class_right C (twist_nonzero hr headnz) good) g hg

/-- The phase index is picked once, before all retained factors. -/
theorem list_common_chart {α : Type} (phase : α→AlgebraicComplex)
    (nonzero : ∀i,phase i≠0) (fs : List (AnySignature AlgebraicComplex))
    (live : ∀f∈fs,f.2≠0) (good : ∃i,Affine (twist (phase i) (listValue fs))) :
    ∃i,∀f∈fs,Affine (twist (phase i) f.2) := by
  obtain ⟨i,hi⟩:=good
  exact ⟨i,list_classes .affine (phase i) (nonzero i) fs live hi⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseWholeFamily
end
