import Holant.Projective.BinaryPencil
import Holant.Certificates.MatchingContractionClosure.Presentation

/-! Exact four-port rooted matching products. The source presentation's
ordered ports, both actual binary factors and global nonzero scalar remain
data. Support and phase statements are derived, without a fixed-ruling input. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil
open Holant Holant.Projective Holant.Certificates.MatchingContractionClosure
open scoped BigOperators

abbrev Word := Fin 4 → Bool
def support (q : Word → ℂ) : Finset Word := Finset.univ.filter (fun x => q x ≠ 0)

@[simp] theorem mem_support (q : Word → ℂ) (x : Word) : x ∈ support q ↔ q x ≠ 0 := by
  classical
  simp [support]

structure Product (m : ℕ) (q : Signature ℂ 4) where
  ports : (Fin 2 × Bool) ≃ Fin 4
  matrix : Fin 2 → Kernel ℂ
  scalar : ℂ
  nonzero : scalar ≠ 0
  rooted : ∀ e, IsRootMonomial m (matrix e)
  equation : q = fun x => scalar * ∏ e, matrix e (x (ports (e,false))) (x (ports (e,true)))

def RootProduct (m : ℕ) (q : Signature ℂ 4) : Prop := Nonempty (Product m q)

theorem root_support {m : ℕ} {B : Kernel ℂ} (h : IsRootMonomial m B) :
    ∃ p : Bool, ∀ a b, B a b ≠ 0 ↔ b = (a ^^ p) := by
  rcases h with ⟨h01,h10,h00,h11,_⟩ | ⟨h00,h11,h01,h10,_⟩
  · refine ⟨false,?_⟩
    intro a b
    cases a <;> cases b <;> simp_all
  · refine ⟨true,?_⟩
    intro a b
    cases a <;> cases b <;> simp_all

theorem root_ratio {m : ℕ} {B : Kernel ℂ} (h : IsRootMonomial m B)
    (a b c d : Bool) (hab : B a b ≠ 0) (hcd : B c d ≠ 0) :
    (B a b / B c d)^m = 1 := by
  have inverse_ratio (z w : ℂ) (hr : (z / w)^m = 1) : (w / z)^m = 1 := by
    rw [show w / z = (z / w)⁻¹ from (inv_div z w).symm, inv_pow, hr, inv_one]
  rcases h with ⟨h01,h10,h00,h11,hr⟩ | ⟨h00,h11,h01,h10,hr⟩
  · cases a <;> cases b <;> cases c <;> cases d <;>
      simp_all [div_self, inverse_ratio]
  · cases a <;> cases b <;> cases c <;> cases d <;>
      simp_all [div_self, inverse_ratio]

def complement (x : Word) : Word := fun i => !(x i)

namespace Product
variable {m : ℕ} {q : Signature ℂ 4} (D : Product m q)

theorem supported (x : Word) : q x ≠ 0 ↔
    ∀ e, D.matrix e (x (D.ports (e,false))) (x (D.ports (e,true))) ≠ 0 := by
  rw [congrFun D.equation x]
  simp [D.nonzero, Finset.prod_ne_zero_iff]

def parity (e : Fin 2) : Bool := Classical.choose (root_support (D.rooted e))

theorem parity_spec (e : Fin 2) (a b : Bool) :
    D.matrix e a b ≠ 0 ↔ b = (a ^^ D.parity e) :=
  Classical.choose_spec (root_support (D.rooted e)) a b

def word (a : Fin 2 → Bool) : Word := fun i =>
  if (D.ports.symm i).2 then a (D.ports.symm i).1 ^^ D.parity (D.ports.symm i).1
  else a (D.ports.symm i).1

@[simp] theorem word_first (a : Fin 2 → Bool) (e : Fin 2) :
    D.word a (D.ports (e,false)) = a e := by
  unfold word
  rw [D.ports.symm_apply_apply]
  rfl

@[simp] theorem word_second (a : Fin 2 → Bool) (e : Fin 2) :
    D.word a (D.ports (e,true)) = (a e ^^ D.parity e) := by
  unfold word
  rw [D.ports.symm_apply_apply]
  rfl

theorem word_supported (a : Fin 2 → Bool) : q (D.word a) ≠ 0 := by
  rw [D.supported]
  intro e
  rw [D.parity_spec]
  simp

def supportEquiv : (Fin 2 → Bool) ≃ {x // x ∈ support q} where
  toFun a := ⟨D.word a, (mem_support q _).mpr (D.word_supported a)⟩
  invFun x e := x.val (D.ports (e,false))
  left_inv a := by funext e; exact D.word_first a e
  right_inv x := by
    apply Subtype.ext
    funext i
    obtain ⟨⟨e,b⟩,rfl⟩ := D.ports.surjective i
    have h := (D.supported x.val).mp ((mem_support q x.val).mp x.property) e
    have hp := (D.parity_spec e _ _).mp h
    cases b
    · simp
    · simpa using hp.symm

include D in
theorem support_card : (support q).card = 4 := by
  classical
  calc
    (support q).card = Fintype.card {x // x ∈ support q} := (Fintype.card_coe _).symm
    _ = Fintype.card (Fin 2 → Bool) := (Fintype.card_congr D.supportEquiv).symm
    _ = 4 := by norm_num

include D in
theorem nonzero_tensor : q ≠ 0 := by
  intro hz
  have h := D.word_supported (fun _ => false)
  simp [hz] at h

include D in
theorem complement_supported (x : Word) : q (complement x) ≠ 0 ↔ q x ≠ 0 := by
  rw [D.supported, D.supported]
  have flip (a b p : Bool) : ((!b) = ((!a) ^^ p)) ↔ b = (a ^^ p) := by
    cases a <;> cases b <;> cases p <;> decide
  simp only [complement,D.parity_spec,flip]

include D in
theorem ratio_roots (x y : Word) (hx : q x ≠ 0) (hy : q y ≠ 0) : (q x / q y)^m = 1 := by
  have hX := (D.supported x).mp hx
  have hY := (D.supported y).mp hy
  have h0 := root_ratio (D.rooted 0) _ _ _ _ (hX 0) (hY 0)
  have h1 := root_ratio (D.rooted 1) _ _ _ _ (hX 1) (hY 1)
  have equation : q x / q y =
      (D.matrix 0 (x (D.ports (0,false))) (x (D.ports (0,true))) /
        D.matrix 0 (y (D.ports (0,false))) (y (D.ports (0,true)))) *
      (D.matrix 1 (x (D.ports (1,false))) (x (D.ports (1,true))) /
        D.matrix 1 (y (D.ports (1,false))) (y (D.ports (1,true)))) := by
    rw [congrFun D.equation x,congrFun D.equation y]
    simp only [Fin.prod_univ_two]
    field_simp [D.nonzero,hY 0,hY 1]
  rw [equation,mul_pow,h0,h1,one_mul]

end Product

theorem of_presentation {m : ℕ} {q : Signature ℂ 4}
    (M : Presentation ℂ (Fin 4)) (rooted : ∀ e, IsRootMonomial m (M.matrix e))
    (scalar : M.scalar ≠ 0) (equation : q = M.tensor) : RootProduct m q := by
  have edges : M.edges = 2 := by
    have h := Fintype.card_congr M.ports
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at h
    omega
  cases M with
  | mk n p A c =>
      dsimp only at edges
      subst n
      exact ⟨⟨p,A,c,scalar,rooted,equation⟩⟩

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil
