import Holant.Projective.BinaryPencil

/-! Literal relation and sampled transfer cards from manuscript Lemma 7.1
(`lem:odd-dih-RN`). Zero samples and overlapping zero endpoint alternatives are
part of the predicates. The diagonal transfer convention is an actual product
with Z, and projective scalars are explicitly nonzero. -/
noncomputable section
namespace Holant.Projective.CyclicPhasePencil

variable {K : Type*} [Field K]

/-- The three source systems, with a single finite-order phase witness. -/
def Relation (m : ℕ) (a b c d : K) : Prop :=
  ∃ α : K, α^m=1 ∧
    ((c= -α*a ∧ d= -α*b) ∨
      (b=0 ∧ c=0 ∧ d=α*a) ∨ (a=0 ∧ d=0 ∧ c=α*b))

/-- Entrywise zero-or-cyclic condition, retaining the displayed port order. -/
def ScalarSample (m : ℕ) (u v : K) : Prop :=
  (u=0 ∧ v=0) ∨ (u≠0 ∧ v≠0 ∧ (v/u)^m=1)

def ScalarSamples (m : ℕ) (a b c d : K) : Prop :=
  ∀ s : K, s^m=1 → ScalarSample m (a-s*b) (-c+s*d)

def diagonal (u v : K) : Kernel K := fun i j =>
  if i=j then if i then v else u else 0

def phase (η : K) : Kernel K := diagonal 1 η
def Z : Kernel K := diagonal 1 (-1)
def card (a b c d s : K) : Kernel K :=
  Kernel.mul (diagonal (a-s*b) (c-s*d)) Z

/-- Literal projective equality to D_eta; no zero multiplier is allowed. -/
def IsPhase (m : ℕ) (T : Kernel K) : Prop :=
  ∃ η lam : K, η^m=1 ∧ lam≠0 ∧ T=lam • phase η

def MatrixSamples (m : ℕ) (a b c d : K) : Prop :=
  ∀ s : K, s^m=1 → card a b c d s=0 ∨ IsPhase m (card a b c d s)

theorem root_ne_zero {m : ℕ} (hm : 0<m) {z : K} (hz : z^m=1) : z≠0 := by
  intro h
  simp [h,Nat.ne_of_gt hm] at hz

theorem card_eq (a b c d s : K) : card a b c d s=diagonal (a-s*b) (-c+s*d) := by
  funext i j
  cases i <;> cases j <;> simp [card,Kernel.mul,Z,diagonal] <;> ring

theorem diagonal_eq_zero_iff (u v : K) : diagonal u v=0 ↔ u=0 ∧ v=0 := by
  constructor
  · intro h
    exact ⟨congrFun (congrFun h false) false,congrFun (congrFun h true) true⟩
  · rintro ⟨rfl,rfl⟩
    funext i j
    cases i <;> cases j <;> rfl

theorem diagonal_isPhase_iff {m : ℕ} (hm : 0<m) (u v : K) :
    IsPhase m (diagonal u v) ↔ u≠0 ∧ v≠0 ∧ (v/u)^m=1 := by
  constructor
  · rintro ⟨η,lam,hη,hlam,h⟩
    have hu : u=lam := by simpa [diagonal,phase] using congrFun (congrFun h false) false
    have hv : v=lam*η := congrFun (congrFun h true) true
    subst u
    subst v
    exact ⟨hlam,mul_ne_zero hlam (root_ne_zero hm hη),by simpa [hlam] using hη⟩
  · rintro ⟨hu,hv,hphase⟩
    refine ⟨v/u,u,hphase,hu,?_⟩
    funext i j
    cases i <;> cases j <;> simp [diagonal,phase,hu,mul_div_cancel₀]

theorem matrixSamples_iff {m : ℕ} (hm : 0<m) (a b c d : K) :
    MatrixSamples m a b c d ↔ ScalarSamples m a b c d := by
  simp only [MatrixSamples,ScalarSamples,card_eq,diagonal_eq_zero_iff,diagonal_isPhase_iff hm,ScalarSample]

@[simp] theorem relation_zero (m : ℕ) : Relation m (0 : K) 0 0 0 :=
  ⟨1,one_pow m,Or.inl ⟨by simp,by simp⟩⟩

end Holant.Projective.CyclicPhasePencil
