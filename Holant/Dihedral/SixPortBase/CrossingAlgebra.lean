import Holant.Dihedral.CompatibleClosure.Monomial
import Mathlib.Data.Finset.Prod

/-! Actual coefficient sums for a crossing of two original binary factors.
The kernel is exactly the phase-one parity kernel, and all nonzero outputs
are products of one unique internal lift. -/
noncomputable section
namespace Holant.Dihedral.SixPortBase.Crossing
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure
set_option backward.isDefEq.respectTransparency false

abbrev PairWord := Bool × Bool

def binarySupport (A : Mat) : Finset PairWord := by
  classical
  exact Finset.univ.filter (fun x => A x.1 x.2 ≠ 0)

@[simp] theorem mem_binarySupport (A : Mat) (x : PairWord) :
    x ∈ binarySupport A ↔ A x.1 x.2 ≠ 0 := by
  classical
  simp [binarySupport]

def point (r s : Bool) (c : Scalar) : Mat :=
  fun u v => if u=r ∧ v=s then c else 0

def IsPoint (A : Mat) : Prop := ∃ r s c, c ≠ 0 ∧ A=point r s c

def contract (γ : Bool) (A B : Mat) : Mat := fuse (M γ 1) A B

theorem contract_sum (γ : Bool) (A B : Mat) (u v : Bool) :
    contract γ A B u v = ∑ i : Bool, ∑ j : Bool,
      M γ 1 i j * (A u i * B j v) := by
  simp only [contract,fuse,Signature.connect,Fintype.sum_bool]
  ring

theorem parity_kernel (γ : Bool) : M γ (1 : Scalar) =
    if γ then Signature.disequality else Signature.equality := by
  funext i j
  cases γ <;> cases i <;> cases j <;>
    simp [M,monomial,Signature.disequality,Signature.equality]

theorem contract_isMonomial (γ : Bool) {A B : Mat}
    (hA : IsMonomial A) (hB : IsMonomial B) : IsMonomial (contract γ A B) := by
  rw [contract,fuse_eq_mul]
  exact (hA.mul (M_isMonomial γ one_ne_zero)).mul hB

theorem contract_monomial_left_value (γ α : Bool) (w : Bool → Scalar)
    (B : Mat) (u v : Bool) :
    contract γ (monomial α w) B u v = w u * B (u ^^ α ^^ γ) v := by
  cases γ <;> cases α <;> cases u <;>
    simp [contract_sum,M,monomial]

/-- The left monomial and parity kernel force both internal bits, even when
 the right factor is only a singleton or is an arbitrary binary. -/
theorem contract_unique_lift_left (γ : Bool) {A : Mat}
    (hA : IsMonomial A) (B : Mat) (u v : Bool) :
    contract γ A B u v ≠ 0 ↔ ∃! ij : PairWord,
      M γ 1 ij.1 ij.2 * (A u ij.1 * B ij.2 v) ≠ 0 := by
  obtain ⟨α,w,hw,rfl⟩ := hA
  rw [contract_monomial_left_value]
  constructor
  · intro h
    refine ⟨(u ^^ α,u ^^ α ^^ γ),?_,?_⟩
    · simpa [M,monomial] using h
    · rintro ⟨i,j⟩ hij
      have hi : i=(u ^^ α) := by
        by_contra hn
        simp [M,monomial,hn] at hij
      have hj : j=(i ^^ γ) := by
        by_contra hn
        simp [M,monomial,hn] at hij
      simp [hi,hj]
  · rintro ⟨⟨i,j⟩,hij,_⟩
    have hi : i=(u ^^ α) := by
      by_contra hn
      simp [M,monomial,hn] at hij
    have hj : j=(i ^^ γ) := by
      by_contra hn
      simp [M,monomial,hn] at hij
    simpa [M,monomial,hi,hj] using hij

theorem contract_unique_lift (γ : Bool) {A B : Mat}
    (hA : IsMonomial A) (_hB : IsMonomial B) (u v : Bool) :
    contract γ A B u v ≠ 0 ↔ ∃! ij : PairWord,
      M γ 1 ij.1 ij.2 * (A u ij.1 * B ij.2 v) ≠ 0 :=
  contract_unique_lift_left γ hA B u v

theorem contract_monomial_right_value (γ β : Bool) (w : Bool → Scalar)
    (A : Mat) (u v : Bool) :
    contract γ A (monomial β w) u v = A u (v ^^ β ^^ γ)*w (v ^^ β) := by
  cases γ <;> cases β <;> cases v <;> simp [contract_sum,M,monomial]

/-- If the fixed nonsingular factor is on the right, the same two internal
bits are forced from the right surviving original port. -/
theorem contract_unique_lift_right (γ : Bool) {B : Mat}
    (A : Mat) (hB : IsMonomial B) (u v : Bool) :
    contract γ A B u v ≠ 0 ↔ ∃! ij : PairWord,
      M γ 1 ij.1 ij.2 * (A u ij.1 * B ij.2 v) ≠ 0 := by
  obtain ⟨β,w,hw,rfl⟩ := hB
  rw [contract_monomial_right_value]
  have force (i j : Bool)
      (hij : M γ 1 i j * (A u i * monomial β w j v) ≠ 0) :
      i=(v ^^ β ^^ γ) ∧ j=(v ^^ β) := by
    have hj : v=(j ^^ β) := by
      by_contra hn
      simp [monomial,hn] at hij
    have hi : j=(i ^^ γ) := by
      by_contra hn
      simp [M,monomial,hn] at hij
    have flip (a b c : Bool) : a=(b ^^ c) → b=(a ^^ c) := by
      cases a <;> cases b <;> cases c <;> decide
    have hj' := flip v j β hj
    have hi' := flip j i γ hi
    exact ⟨hi'.trans (congrArg (· ^^ γ) hj'),hj'⟩
  constructor
  · intro h
    refine ⟨(v ^^ β ^^ γ,v ^^ β),?_,?_⟩
    · cases β <;> cases γ <;> cases v <;> simpa [M,monomial] using h
    · rintro ⟨i,j⟩ hij
      obtain ⟨hi,hj⟩ := force i j hij
      simp [hi,hj]
  · rintro ⟨⟨i,j⟩,hij,_⟩
    obtain ⟨hi,hj⟩ := force i j hij
    subst i; subst j
    cases β <;> cases γ <;> cases v <;> simpa [M,monomial] using hij

theorem monomial_support_card {A : Mat} (hA : IsMonomial A) :
    (binarySupport A).card=2 := by
  classical
  obtain ⟨α,w,hw,rfl⟩ := hA
  have he : binarySupport (monomial α w) =
      Finset.univ.image (fun b : Bool => (b,b ^^ α)) := by
    ext ⟨a,b⟩
    cases α <;> cases a <;> cases b <;> simp [monomial,hw]
  rw [he,Finset.card_image_of_injective]
  · rfl
  · intro a b h
    exact congrArg Prod.fst h

theorem monomial_complementary {A : Mat} (hA : IsMonomial A) (u v : Bool) :
    A (!u) (!v) ≠ 0 ↔ A u v ≠ 0 := by
  obtain ⟨α,w,hw,rfl⟩ := hA
  cases α <;> cases u <;> cases v <;> simp [monomial,hw]

theorem contract_two_complementary (γ : Bool) {A B : Mat}
    (hA : IsMonomial A) (hB : IsMonomial B) :
    (binarySupport (contract γ A B)).card=2 ∧
      ∀ u v,contract γ A B (!u) (!v) ≠ 0 ↔ contract γ A B u v ≠ 0 :=
  ⟨monomial_support_card (contract_isMonomial γ hA hB),
    monomial_complementary (contract_isMonomial γ hA hB)⟩

theorem point_support {r s : Bool} {c : Scalar} (hc : c ≠ 0) :
    binarySupport (point r s c) = {(r,s)} := by
  classical
  ext ⟨u,v⟩
  simp [point,hc,Prod.ext_iff]

theorem point_support_card {A : Mat} (hA : IsPoint A) :
    (binarySupport A).card=1 := by
  obtain ⟨r,s,c,hc,rfl⟩ := hA
  rw [point_support hc]
  rfl

theorem contract_point_right_value (γ α r s : Bool) (w : Bool → Scalar) (c : Scalar) :
    contract γ (monomial α w) (point r s c) =
      point (r ^^ γ ^^ α) s (w (r ^^ γ ^^ α)*c) := by
  funext u v
  cases γ <;> cases α <;> cases r <;> cases s <;> cases u <;> cases v <;>
    simp [contract_sum,M,monomial,point]

theorem contract_point_left_value (γ β r s : Bool) (w : Bool → Scalar) (c : Scalar) :
    contract γ (point r s c) (monomial β w) =
      point r (s ^^ γ ^^ β) (c*w (s ^^ γ)) := by
  funext u v
  cases γ <;> cases β <;> cases r <;> cases s <;> cases u <;> cases v <;>
    simp [contract_sum,M,monomial,point]

theorem contract_point_right (γ : Bool) {A B : Mat}
    (hA : IsMonomial A) (hB : IsPoint B) : IsPoint (contract γ A B) := by
  obtain ⟨α,w,hw,rfl⟩ := hA
  obtain ⟨r,s,c,hc,rfl⟩ := hB
  exact ⟨r ^^ γ ^^ α,s,_,mul_ne_zero (hw _) hc,contract_point_right_value _ _ _ _ _ _⟩

theorem contract_point_left (γ : Bool) {A B : Mat}
    (hA : IsPoint A) (hB : IsMonomial B) : IsPoint (contract γ A B) := by
  obtain ⟨r,s,c,hc,rfl⟩ := hA
  obtain ⟨β,w,hw,rfl⟩ := hB
  exact ⟨r,s ^^ γ ^^ β,_,mul_ne_zero hc (hw _),contract_point_left_value _ _ _ _ _ _⟩

theorem contract_transpose (γ : Bool) (A B : Mat) :
    Kernel.transpose (contract γ A B) =
      contract γ (Kernel.transpose B) (Kernel.transpose A) := by
  funext u v
  cases γ <;> simp [Kernel.transpose,contract_sum,M,monomial] <;> ring

theorem IsPoint.transpose {A : Mat} (hA : IsPoint A) : IsPoint (Kernel.transpose A) := by
  obtain ⟨r,s,c,hc,rfl⟩ := hA
  refine ⟨s,r,c,hc,?_⟩
  funext u v
  simp [Kernel.transpose,point,and_comm]

end Holant.Dihedral.SixPortBase.Crossing
