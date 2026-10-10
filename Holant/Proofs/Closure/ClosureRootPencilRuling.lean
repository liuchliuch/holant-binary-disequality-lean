import Holant.Proofs.Closure.ClosureRootPencilGenericSegre
import Holant.Proofs.Closure.ClosureRootPencilBinary

/-! Closed, zero-safe four-port fixed-ruling producer. The fixed binary,
saved original port order, full endpoint equations and varying binary's root
condition are conclusions from the actual sampled root products. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil
open Holant Holant.Projective

structure Ruling (m : ℕ) (U V : Signature ℂ 4) where
  ports : (Fin 2 × Bool) ≃ Fin 4
  fixed : Kernel ℂ
  fixedRoot : IsRootMonomial m fixed
  variable0 : Kernel ℂ
  variable1 : Kernel ℂ
  endpoint0 : U=pairTensor ports fixed variable0
  endpoint1 : V=pairTensor ports fixed variable1
  samples : ∀ t : ℂ, t^m=1 → binaryPencil variable0 variable1 t=0 ∨
    IsRootMonomial m (binaryPencil variable0 variable1 t)

def standardPorts : (Fin 2 × Bool) ≃ Fin 4 :=
  (Fintype.equivFin (Fin 2 × Bool)).trans (finCongr (by simp))

def swapPorts (p : (Fin 2 × Bool) ≃ Fin 4) : (Fin 2 × Bool) ≃ Fin 4 :=
  (Equiv.prodCongr (Equiv.swap (0 : Fin 2) 1) (Equiv.refl Bool)).trans p

@[simp] theorem swapPorts_first (p : (Fin 2 × Bool) ≃ Fin 4) (a : Bool) :
    swapPorts p (0,a)=p (1,a) := by simp [swapPorts]

@[simp] theorem swapPorts_second (p : (Fin 2 × Bool) ≃ Fin 4) (a : Bool) :
    swapPorts p (1,a)=p (0,a) := by simp [swapPorts]

theorem pairTensor_swap (p : (Fin 2 × Bool) ≃ Fin 4) (C D : Kernel ℂ) :
    pairTensor (swapPorts p) C D=pairTensor p D C := by
  funext x
  simp only [pairTensor,swapPorts_first,swapPorts_second]
  exact mul_comm _ _

def zeroRuling (m : ℕ) : Ruling m 0 0 where
  ports := standardPorts
  fixed := parityCoordinates false 1 1
  fixedRoot := (isRootMonomial_parityCoordinates_iff m false 1 1).mpr (by norm_num)
  variable0 := 0
  variable1 := 0
  endpoint0 := by funext x;simp [pairTensor]
  endpoint1 := by funext x;simp [pairTensor]
  samples t _ := Or.inl (by funext a b;change 0+t*0=0;ring)

theorem ruling_nonzero_pencil {m : ℕ} (hm : 3 ≤ m) (U V : Signature ℂ 4)
    (nonzero : U≠0 ∨ V≠0)
    (samples : ∀ t : ℂ, t^m=1 → pencil U V t=0 ∨ RootProduct m (pencil U V t)) :
    Nonempty (Ruling m U V) := by
  obtain ⟨t0,ht0,actual⟩ := exists_root_anchor hm U V nonzero samples
  obtain ⟨P⟩ := actual
  have anchorSupport : support (pencil U V t0)=unionSupport U V :=
    sampled_support_exact hm U V samples t0 ht0 P.nonzero_tensor
  have outsideU (x : Word) (hx : pencil U V t0 x=0) : U x=0 := by
    apply not_ne_iff.mp
    intro hn
    have mem : x ∈ support (pencil U V t0) := by
      rw [anchorSupport]
      exact (ClosureRootPencilCount.mem_unionSupport U V x).mpr (Or.inl hn)
    exact (mem_support _ x).mp mem hx
  have outsideV (x : Word) (hx : pencil U V t0 x=0) : V x=0 := by
    apply not_ne_iff.mp
    intro hn
    have mem : x ∈ support (pencil U V t0) := by
      rw [anchorSupport]
      exact (ClosureRootPencilCount.mem_unionSupport U V x).mpr (Or.inr hn)
    exact (mem_support _ x).mp mem hx
  have anchorSubset : ∀ t : ℂ, t^m=1 → pencil U V t≠0 →
      support (pencil U V t0) ⊆ support (pencil U V t) := by
    intro t ht hn
    rw [anchorSupport,sampled_support_exact hm U V samples t ht hn]
  let a : Bool → ℂ := fun i => P.scalar*P.weight 0 i
  let b : Bool → ℂ := P.weight 1
  have ha : ∀ i, a i ≠ 0 := fun i => mul_ne_zero P.nonzero (P.weight_nonzero 0 i)
  have hb : ∀ j, b j ≠ 0 := P.weight_nonzero 1
  have anchor : coordinates P U+t0 • coordinates P V=(fun i j => a i*b j) := by
    funext i j
    exact P.anchor_coordinates i j
  have minors : ∀ s t : ℂ,
      (s*coordinates P U false false+t*coordinates P V false false)*
        (s*coordinates P U true true+t*coordinates P V true true)-
      (s*coordinates P U false true+t*coordinates P V false true)*
        (s*coordinates P U true false+t*coordinates P V true false)=0 := by
    intro s t
    exact all_coordinates_span_det hm U V samples t0 ht0 P s t
  rcases Matrix.coordinate_linear_ruling (coordinates P U) (coordinates P V) t0 a b ha hb anchor minors with
    left | right
  · have simplify (Q : Signature ℂ 4)
        (h : ∀ i j, coordinates P Q i j=a i*(coordinates P Q false j/a false)) :
        ∀ i j, coordinates P Q i j=P.weight 0 i*(coordinates P Q false j/P.weight 0 false) := by
      intro i j
      rw [h]
      dsimp [a]
      field_simp [P.nonzero,P.weight_nonzero 0 false]
    exact ⟨{
      ports := P.ports
      fixed := P.matrix 0
      fixedRoot := P.rooted 0
      variable0 := P.leftVariable U
      variable1 := P.leftVariable V
      endpoint0 := P.left_reconstruct U outsideU (simplify U left.1)
      endpoint1 := P.left_reconstruct V outsideV (simplify V left.2)
      samples := P.leftVariable_samples U V samples anchorSubset }⟩
  · exact ⟨{
      ports := swapPorts P.ports
      fixed := P.matrix 1
      fixedRoot := P.rooted 1
      variable0 := P.rightVariable U
      variable1 := P.rightVariable V
      endpoint0 := (P.right_reconstruct U outsideU right.1).trans (pairTensor_swap _ _ _).symm
      endpoint1 := (P.right_reconstruct V outsideV right.2).trans (pairTensor_swap _ _ _).symm
      samples := P.rightVariable_samples U V samples anchorSubset }⟩

/-- The manuscript four-port sector ruling, including the all-zero sector,
proportional endpoints and zero root samples. There is no supplied matching,
factor, normalization or successful classification state. -/
theorem fixed_ruling {m : ℕ} (hm : 3 ≤ m) (U V : Signature ℂ 4)
    (samples : ∀ t : ℂ, t^m=1 → pencil U V t=0 ∨ RootProduct m (pencil U V t)) :
    Nonempty (Ruling m U V) := by
  by_cases hu : U=0
  · by_cases hv : V=0
    · subst U
      subst V
      exact ⟨zeroRuling m⟩
    · exact ruling_nonzero_pencil hm U V (Or.inr hv) samples
  · exact ruling_nonzero_pencil hm U V (Or.inl hu) samples

def ruling {m : ℕ} (hm : 3 ≤ m) (U V : Signature ℂ 4)
    (samples : ∀ t : ℂ, t^m=1 → pencil U V t=0 ∨ RootProduct m (pencil U V t)) :
    Ruling m U V := Classical.choice (fixed_ruling hm U V samples)

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureRootPencil
