import Holant.ReedMuller.RadonAccess.Directions

/-! The nondegenerate two-plane, its orthogonal complement, and the actual
translation-orbit quotient in Lemma 7.15. -/
namespace Holant.ReedMuller.RadonAccess
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

structure RadonFrame (n : ℕ) where
  A : OrthogonalMap n
  i : Fin n
  j : Fin n
  distinct : i ≠ j

@[simp] theorem binary_add_self (x : BinaryVector n) : x + x = 0 := by
  funext i
  exact add_self_zero (x i)

@[simp] theorem binary_two_nsmul (x : BinaryVector n) : (2 : ℕ) • x = 0 := by
  rw [two_nsmul,binary_add_self]

@[simp] theorem scalar_two_nsmul (x : ZMod 2) : (2 : ℕ) • x = 0 := by
  rw [two_nsmul,add_self_zero]

@[simp] theorem binary_two : (2 : BinaryVector n) = 0 := by
  funext i
  change (2 : ZMod 2) = 0
  decide

@[simp] theorem scalar_two : (2 : ZMod 2) = 0 := by decide

namespace RadonFrame

def r (F : RadonFrame n) : BinaryVector n := F.A.symm (unitWord F.i)
def v (F : RadonFrame n) : BinaryVector n := F.A.symm (unitWord F.i + unitWord F.j)

@[simp] theorem map_r (F : RadonFrame n) : F.A F.r = unitWord F.i :=
  F.A.apply_symm_apply _
@[simp] theorem map_v (F : RadonFrame n) : F.A F.v = unitWord F.i + unitWord F.j :=
  F.A.apply_symm_apply _
@[simp] theorem dot_rr (F : RadonFrame n) : dot F.r F.r = 1 := by
  rw [← F.A.isometry, map_r, dot_unit_left]
  simp
@[simp] theorem dot_rv (F : RadonFrame n) : dot F.r F.v = 1 := by
  rw [← F.A.isometry, map_r, map_v, dot_add_right, dot_unit_left, dot_unit_left]
  simp [F.distinct]
@[simp] theorem dot_vr (F : RadonFrame n) : dot F.v F.r = 1 := by
  rw [dot_comm, dot_rv]
@[simp] theorem dot_vv (F : RadonFrame n) : dot F.v F.v = 0 := by
  rw [← F.A.isometry, map_v, ← cast_binaryWeight, weight_pair _ _ F.distinct]
  decide

theorem v_ne_zero (F : RadonFrame n) : F.v ≠ 0 := by
  intro h
  have hh := F.dot_rv
  rw [h] at hh
  simpa [dot] using hh

def plane (F : RadonFrame n) : BinaryCode n := Submodule.span (ZMod 2) {F.r,F.v}

def complement (F : RadonFrame n) : BinaryCode n where
  carrier := {w | dot F.r w = 0 ∧ dot F.v w = 0}
  zero_mem' := by simp [dot]
  add_mem' := by
    rintro x y ⟨hx,hx'⟩ ⟨hy,hy'⟩
    simp [dot_add_right,hx,hx',hy,hy']
  smul_mem' := by
    rintro c x ⟨hx,hx'⟩
    simp [dot_smul_right,hx,hx']

@[simp] theorem mem_complement (F : RadonFrame n) (w : BinaryVector n) :
    w ∈ F.complement ↔ dot F.r w = 0 ∧ dot F.v w = 0 := Iff.rfl

theorem mem_plane (F : RadonFrame n) (x : BinaryVector n) :
    x ∈ F.plane ↔ ∃ a b : ZMod 2, a • F.r + b • F.v = x := Submodule.mem_span_pair

/-- This is exactly the ambient-relative orthogonal complement of the span. -/
theorem complement_iff_orthogonal_plane (F : RadonFrame n) (w : BinaryVector n) :
    w ∈ F.complement ↔ ∀ p ∈ F.plane, dot p w = 0 := by
  constructor
  · rintro ⟨hr,hv⟩ p hp
    obtain ⟨a,b,rfl⟩ := (F.mem_plane p).mp hp
    simp [dot_add_left,dot_smul_left,hr,hv]
  · intro h
    exact ⟨h F.r (Submodule.subset_span (by simp)),
      h F.v (Submodule.subset_span (by simp))⟩

/-- The explicit two-plane projection, with its two recorded coefficients. -/
def planePart (F : RadonFrame n) (x : BinaryVector n) : BinaryVector n :=
  dot F.v x • F.r + (dot F.r x + dot F.v x) • F.v

def complementPart (F : RadonFrame n) (x : BinaryVector n) : BinaryVector n := x + F.planePart x

theorem planePart_mem (F : RadonFrame n) (x : BinaryVector n) : F.planePart x ∈ F.plane :=
  (F.mem_plane _).mpr ⟨_,_,rfl⟩

theorem complementPart_mem (F : RadonFrame n) (x : BinaryVector n) :
    F.complementPart x ∈ F.complement := by
  simp only [mem_complement,complementPart,planePart,dot_add_right,dot_smul_right,
    dot_rr,dot_rv,dot_vr,dot_vv,mul_one,mul_zero,add_zero]
  constructor <;> abel_nf <;> simp

theorem decomposition (F : RadonFrame n) (x : BinaryVector n) :
    x = F.planePart x + F.complementPart x := by
  rw [complementPart,add_left_comm,binary_add_self,add_zero]

theorem plane_inter_complement (F : RadonFrame n) {x : BinaryVector n}
    (hp : x ∈ F.plane) (hw : x ∈ F.complement) : x = 0 := by
  obtain ⟨a,b,rfl⟩ := (F.mem_plane x).mp hp
  have ha : a = 0 := by
    simpa [dot_add_right,dot_smul_right] using hw.2
  have hb : b = 0 := by
    simpa [dot_add_right,dot_smul_right,ha] using hw.1
  simp [ha,hb]

/-- The orthogonal direct sum is witnessed by literal summands and uniqueness. -/
theorem exists_unique_decomposition (F : RadonFrame n) (x : BinaryVector n) :
    ∃! pw : F.plane × F.complement, x = (pw.1 : BinaryVector n) + pw.2 := by
  refine ⟨⟨⟨F.planePart x,F.planePart_mem x⟩,⟨F.complementPart x,F.complementPart_mem x⟩⟩,
    F.decomposition x, ?_⟩
  rintro ⟨⟨p,hp⟩,⟨w,hw⟩⟩ h
  have hsum : p + F.planePart x = w + F.complementPart x := by
    rw [complementPart, h]
    abel_nf
    simp
  have hz : p + F.planePart x = 0 := F.plane_inter_complement
    (F.plane.add_mem hp (F.planePart_mem x))
    (hsum ▸ F.complement.add_mem hw (F.complementPart_mem x))
  have heqp : p = F.planePart x := by
    have hh := congrArg (fun z => z + F.planePart x) hz
    simpa [add_assoc] using hh
  have heqw : w = F.complementPart x := by
    have hh := congrArg (fun z => z + p) h
    rw [complementPart,←heqp]
    have hc : p + w + p = w := by rw [add_right_comm,binary_add_self,zero_add]
    simpa only [hc] using hh.symm
  apply Prod.ext <;> apply Subtype.ext
  · exact heqp
  · exact heqw

/-- The form on the remaining space is nondegenerate. -/
theorem complement_nondegenerate (F : RadonFrame n) (w : F.complement)
    (h : ∀ z : F.complement, dot (w : BinaryVector n) (z : BinaryVector n) = 0) : (w : BinaryVector n) = 0 := by
  apply dot_ext
  intro x
  conv_lhs => rw [F.decomposition x]
  rw [dot_add_right]
  have hp : dot (w : BinaryVector n) (F.planePart x) = 0 := by
    rw [dot_comm]
    exact (F.complement_iff_orthogonal_plane w).mp w.property _ (F.planePart_mem x)
  rw [hp,h ⟨F.complementPart x,F.complementPart_mem x⟩]
  simp [dot]

/-- The hyperplane is defined in the original input coordinates. -/
def Hyperplane (F : RadonFrame n) (ε : ZMod 2) := {x : BinaryVector n // dot x F.v = ε}

/-- Its actual two-point translation-orbit relation. -/
def orbitRel (F : RadonFrame n) (ε : ZMod 2) (x y : F.Hyperplane ε) : Prop :=
  x.1 = y.1 ∨ x.1 = y.1 + F.v

def orbitSetoid (F : RadonFrame n) (ε : ZMod 2) : Setoid (F.Hyperplane ε) where
  r := F.orbitRel ε
  iseqv := by
    refine ⟨fun _ => Or.inl rfl, ?_, ?_⟩
    · intro x y h
      rcases h with h | h
      · exact Or.inl h.symm
      · right
        rw [h,add_assoc,binary_add_self,add_zero]
    · intro x y z hxy hyz
      rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
      · exact Or.inl (hxy.trans hyz)
      · exact Or.inr (hxy.trans hyz)
      · exact Or.inr (by rw [hxy,hyz])
      · left
        rw [hxy,hyz,add_assoc,binary_add_self,add_zero]

abbrev Orbit (F : RadonFrame n) (ε : ZMod 2) := Quotient (F.orbitSetoid ε)

def orbit (F : RadonFrame n) (ε : ZMod 2) (x : F.Hyperplane ε) : F.Orbit ε := Quotient.mk _ x

@[simp] theorem orbit_eq_iff (F : RadonFrame n) (ε : ZMod 2) (x y : F.Hyperplane ε) :
    F.orbit ε x = F.orbit ε y ↔ x.1 = y.1 ∨ x.1 = y.1 + F.v := Quotient.eq

/-- The source map, as a literal map into an actual quotient type. -/
def iota (F : RadonFrame n) (ε : ZMod 2) (w : F.complement) : F.Orbit ε :=
  F.orbit ε ⟨ε • F.r + w, by
    rw [dot_add_left,dot_smul_left,F.dot_rv,mul_one,dot_comm w F.v,w.property.2,add_zero]⟩

/-- A canonical representative in the orthogonal complement. -/
def quotientCoordinate (F : RadonFrame n) (ε : ZMod 2) (x : F.Hyperplane ε) : F.complement :=
  ⟨x.1 + ε • F.r + (dot x.1 F.r + ε) • F.v, by
    have hv := x.property
    rw [dot_comm] at hv
    simp only [mem_complement,dot_add_right,dot_smul_right,F.dot_rr,F.dot_rv,F.dot_vr,
      F.dot_vv,mul_one,mul_zero,add_zero,hv]
    constructor
    · rw [dot_comm F.r x.1]; abel_nf; simp
    · exact add_self_zero ε⟩

theorem quotientCoordinate_invariant (F : RadonFrame n) (ε : ZMod 2)
    (x y : F.Hyperplane ε) (h : F.orbitRel ε x y) :
    F.quotientCoordinate ε x = F.quotientCoordinate ε y := by
  apply Subtype.ext
  rcases h with h | h
  · simp only [quotientCoordinate,h]
  · simp only [quotientCoordinate,h,dot_add_left,F.dot_vr]
    rw [add_assoc (dot y.1 F.r) 1 ε, add_comm 1 ε, ← add_assoc, add_smul,one_smul]
    abel_nf
    simp

def quotientToComplement (F : RadonFrame n) (ε : ZMod 2) : F.Orbit ε → F.complement :=
  Quotient.lift (F.quotientCoordinate ε) (F.quotientCoordinate_invariant ε)

theorem quotientToComplement_iota (F : RadonFrame n) (ε : ZMod 2) (w : F.complement) :
    F.quotientToComplement ε (F.iota ε w) = w := by
  apply Subtype.ext
  change _ + _ + _ = (w : BinaryVector n)
  have hr : dot (w : BinaryVector n) F.r = 0 := by rw [dot_comm]; exact w.property.1
  simp only [dot_add_left,dot_smul_left,F.dot_rr,mul_one,hr,add_zero,add_self_zero,
    zero_smul,add_zero]
  abel_nf
  simp

theorem iota_quotientToComplement (F : RadonFrame n) (ε : ZMod 2) (q : F.Orbit ε) :
    F.iota ε (F.quotientToComplement ε q) = q := by
  induction q using Quotient.inductionOn with
  | h x =>
    apply Quotient.sound
    change ε • F.r + (x.1 + ε • F.r + (dot x.1 F.r + ε) • F.v) = x.1 ∨
      ε • F.r + (x.1 + ε • F.r + (dot x.1 F.r + ε) • F.v) = x.1 + F.v
    have h : dot x.1 F.r + ε = 0 ∨ dot x.1 F.r + ε = 1 := by
      have hh : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      exact hh _
    rcases h with h | h
    · left; rw [h,zero_smul,add_zero]; abel_nf; simp
    · right; rw [h,one_smul]; abel_nf; simp

/-- The displayed affine slice parametrizes every orbit exactly once. -/
def quotientEquiv (F : RadonFrame n) (ε : ZMod 2) : F.complement ≃ F.Orbit ε where
  toFun := F.iota ε
  invFun := F.quotientToComplement ε
  left_inv := F.quotientToComplement_iota ε
  right_inv := F.iota_quotientToComplement ε

/-- On the translation hyperplane the form agrees with the literal
representative dot product, so it descends without a choice ambiguity. -/
theorem quotientCoordinate_dot (F : RadonFrame n) (x y : F.Hyperplane 0) :
    dot (F.quotientCoordinate 0 x : BinaryVector n) (F.quotientCoordinate 0 y : BinaryVector n) = dot x.1 y.1 := by
  have hx := x.property
  have hy := y.property
  have hy' : dot F.v y.1 = 0 := by rw [dot_comm]; exact hy
  simp [quotientCoordinate,dot_add_left,dot_add_right,dot_smul_left,dot_smul_right,
    hx,hy,hy']

def quotientDot (F : RadonFrame n) (x y : F.Orbit 0) : ZMod 2 :=
  dot (F.quotientToComplement 0 x : BinaryVector n) (F.quotientToComplement 0 y : BinaryVector n)

theorem quotientDot_orbit (F : RadonFrame n) (x y : F.Hyperplane 0) :
    F.quotientDot (F.orbit 0 x) (F.orbit 0 y) = dot x.1 y.1 :=
  F.quotientCoordinate_dot x y

@[simp] theorem iota_isometry (F : RadonFrame n) (w z : F.complement) :
    F.quotientDot (F.iota 0 w) (F.iota 0 z) = dot (w : BinaryVector n) z := by
  simp [quotientDot,quotientToComplement_iota]

end RadonFrame
end
end Holant.ReedMuller.RadonAccess
