import Holant.Proofs.Hardness.EOBinaryPlanePortAccess

/-! Internally select both an original opposite-pair plane and the unique
missing binary word. The resulting three nonzero coefficients are original
values in a literal original-port permutation; no pin or new label is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexPlaneThreeSupportData
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace C
export EOBinaryPlaneCore (word lift compress normalized normalized_lift lift_eo)
end C
namespace O
export FiveSupportEOOrdering (middleCoeff)
end O
namespace R
export EOBinaryPlaneOrient (oriented three_orientation)
end R
namespace A
export EOBinaryPlanePortAccess (output output_lift source output_algebraic)
end A
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K]

def support {n : ℕ} (f : Signature K n) : Finset (Fin n→Bool) := by
  classical
  exact Finset.univ.filter fun x=>f x≠0

@[simp] theorem mem_support {n : ℕ} (f : Signature K n) (x : Fin n→Bool) :
    x∈support f ↔ f x≠0 := by
  classical
  simp [support]

def assignmentPerm {n : ℕ} (p : Equiv.Perm (Fin n)) : Equiv.Perm (Fin n→Bool) where
  toFun x := fun i=>x (p i)
  invFun x := fun i=>x (p.symm i)
  left_inv x := by funext i; simp
  right_inv x := by funext i; simp

theorem support_reindex {n : ℕ} (f : Signature K n) (p : Equiv.Perm (Fin n)) :
    support (Tensor.reindex p f)=(support f).map (assignmentPerm p).symm.toEmbedding := by
  classical
  ext x
  simp only [mem_support,Finset.mem_map]
  constructor
  · intro hx
    exact ⟨assignmentPerm p x,hx,by simp⟩
  · rintro ⟨y,hy,rfl⟩
    change f (assignmentPerm p ((assignmentPerm p).symm y))≠0
    simpa using hy

theorem support_card_reindex {n : ℕ} (f : Signature K n) (p : Equiv.Perm (Fin n)) :
    (support (Tensor.reindex p f)).card=(support f).card := by
  rw [support_reindex,Finset.card_map]

private theorem word_injective : Function.Injective C.word := by
  intro x y h
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  funext i
  fin_cases i
  · exact h0
  · exact h2

theorem support_lift (f : Signature K 2) : support (C.lift f)=(support f).image C.word := by
  classical
  ext x
  simp only [mem_support,Finset.mem_image]
  constructor
  · intro hx
    have hh : x 1=!(x 0) ∧ x 3=!(x 2) := by
      by_contra h
      exact hx (by simp [C.lift,h])
    refine ⟨![x 0,x 2],?_,?_⟩
    · simpa [C.lift,hh] using hx
    · funext i
      fin_cases i <;> simp [C.word,hh.1,hh.2]
  · rintro ⟨z,hz,rfl⟩
    have he : (![z 0,z 1] : Fin 2→Bool)=z := by funext i; fin_cases i <;> rfl
    simpa [C.lift,C.word,he] using hz

theorem support_card_lift (f : Signature K 2) : (support (C.lift f)).card=(support f).card := by
  classical
  rw [support_lift,Finset.card_image_of_injective _ word_injective]

def Plane (M : Signature K 4) : Prop := ∃i : Fin 6,O.middleCoeff M i=0 ∧ O.middleCoeff M (5-i)=0
def ExactlyThree (M : Signature K 4) : Prop := (support M).card=3

def planeIndex (M : Signature K 4) (hp : Plane M) : Fin 6 := Classical.choose hp

theorem plane_zero (M : Signature K 4) (hp : Plane M) :
    O.middleCoeff M (planeIndex M hp)=0 ∧ O.middleCoeff M (5-planeIndex M hp)=0 :=
  Classical.choose_spec hp

def binary (M : Signature K 4) (hp : Plane M) : Signature K 2 :=
  C.compress (C.normalized M (planeIndex M hp))

theorem binary_three (M : Signature K 4) (hp : Plane M)
    (he : DenseEOUnitLocal.EOSupport M) (ht : ExactlyThree M) : (support (binary M hp)).card=3 := by
  have hh := C.normalized_lift M he (planeIndex M hp) (plane_zero M hp).1 (plane_zero M hp).2
  rw [←support_card_lift,show C.lift (binary M hp)=C.normalized M (planeIndex M hp) from hh]
  exact (support_card_reindex M _).trans ht

/-- Three entries among the four binary words have a unique missing word. -/
theorem missing_exists (f : Signature K 2) (hf : (support f).card=3) :
    ∃w : Fin 2→Bool,f w=0 ∧ ∀z,z≠w → f z≠0 := by
  classical
  let Z := Finset.univ.filter fun z : Fin 2→Bool=>f z=0
  have hadd := Finset.card_filter_add_card_filter_not (s:=Finset.univ) (fun z : Fin 2→Bool=>f z=0)
  have hz : Z.card=1 := by
    change Z.card+(support f).card=4 at hadd
    omega
  obtain ⟨w,hw⟩ := Finset.card_eq_one.mp hz
  have hwz : f w=0 := by
    have : w∈Z := by rw [hw]; simp
    simpa [Z] using this
  refine ⟨w,hwz,?_⟩
  intro z hzw hfz
  have : z∈Z := by simp [Z,hfz]
  rw [hw] at this
  exact hzw (Finset.mem_singleton.mp this)

def missing (M : Signature K 4) (hp : Plane M) (he : DenseEOUnitLocal.EOSupport M)
    (ht : ExactlyThree M) : Fin 2→Bool := Classical.choose (missing_exists (binary M hp) (binary_three M hp he ht))

def normalizedBinary (M : Signature K 4) (hp : Plane M) (he : DenseEOUnitLocal.EOSupport M)
    (ht : ExactlyThree M) : Signature K 2 := R.oriented (binary M hp) (missing M hp he ht)

theorem normalized_entries (M : Signature K 4) (hp : Plane M) (he : DenseEOUnitLocal.EOSupport M)
    (ht : ExactlyThree M) :
    normalizedBinary M hp he ht ![false,false]≠0 ∧ normalizedBinary M hp he ht ![false,true]≠0 ∧
    normalizedBinary M hp he ht ![true,false]≠0 ∧ normalizedBinary M hp he ht ![true,true]=0 := by
  have h := Classical.choose_spec (missing_exists (binary M hp) (binary_three M hp he ht))
  exact R.three_orientation _ _ h.1 h.2

def output (M : Signature K 4) (hp : Plane M) (he : DenseEOUnitLocal.EOSupport M)
    (ht : ExactlyThree M) : Signature K 4 := A.output M (planeIndex M hp) (missing M hp he ht)

theorem output_lift (M : Signature K 4) (hp : Plane M) (he : DenseEOUnitLocal.EOSupport M)
    (ht : ExactlyThree M) : output M hp he ht=C.lift (normalizedBinary M hp he ht) :=
  A.output_lift M he (planeIndex M hp) (plane_zero M hp).1 (plane_zero M hp).2 _

theorem output_eo (M : Signature K 4) (hp : Plane M) (he : DenseEOUnitLocal.EOSupport M)
    (ht : ExactlyThree M) : DenseEOUnitLocal.EOSupport (output M hp he ht) := by
  rw [output_lift]
  exact C.lift_eo _

theorem output_corners (M : Signature K 4) (hp : Plane M) (he : DenseEOUnitLocal.EOSupport M)
    (ht : ExactlyThree M) : (entries (output M hp he ht)).b=0 ∧ (entries (output M hp he ht)).y=0 := by
  rw [output_lift]
  simp [entries,C.lift]

variable {L : Type} [Field L] [Algebra ℚ L]
variable (M : Signature L 4) (halg : ∀x,IsAlgebraic ℚ (M x)) (hp : Plane M)
variable (he : DenseEOUnitLocal.EOSupport M) (ht : ExactlyThree M)

abbrev output_algebraic := A.output_algebraic M halg (planeIndex M hp) (missing M hp he ht)
abbrev portSource := A.source M halg (planeIndex M hp) (missing M hp he ht)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexPlaneThreeSupportData
