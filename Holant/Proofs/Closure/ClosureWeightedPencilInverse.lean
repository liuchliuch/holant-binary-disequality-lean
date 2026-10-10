import Holant.Proofs.Closure.ClosureWeightedPencilClassification

/-! Exact inverse port-weight transport of a fixed ruling. Even and odd
pencils may use different gauges. No tensor is asserted to have a fresh
all-permutation native-X deck after either gauge. New proof, awaiting check. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
open Holant Holant.Tractable Holant.Projective Holant.Marked Holant.Marked.SupportAtlas
open Holant.LocalDrafts.MainChain
open ClosureRootPencil
open scoped BigOperators

def complexWeights (r : Fin 4 → Scalar) : Fin 4 → ℂ := fun i => (r i : ℂ)

theorem complexWeights_nonzero (r : Fin 4 → Scalar) (nonzero : ∀ i,r i≠0) :
    ∀ i,complexWeights r i≠0 := by
  intro i
  change (r i : ℂ)≠0
  exact_mod_cast nonzero i

theorem complex_gauge (r : Fin 4 → Scalar) (U : Signature Scalar 4) :
    complexTensor (WeightedGauge.gauge r U)=
      WeightedGauge.gauge (complexWeights r) (complexTensor U) := by
  funext x
  change CyclicBoundary.AlgebraicRepresentatives.inclusion
      ((∏ i,WeightedGauge.bitWeight (r i) (x i))*U x)=
    (∏ i,WeightedGauge.bitWeight (CyclicBoundary.AlgebraicRepresentatives.inclusion (r i)) (x i))*
      CyclicBoundary.AlgebraicRepresentatives.inclusion (U x)
  rw [map_mul,map_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  cases x i <;> simp [WeightedGauge.bitWeight]

theorem complex_gauge_inverse (r : Fin 4 → Scalar) (nonzero : ∀ i,r i≠0)
    (U : Signature Scalar 4) :
    WeightedGauge.gauge (fun i => (complexWeights r i)⁻¹)
      (complexTensor (WeightedGauge.gauge r U))=complexTensor U := by
  rw [complex_gauge]
  exact WeightedGauge.gauge_inverse _ (complexWeights_nonzero r nonzero) _

def portBinary (r : Fin 4 → ℂ) (ports : (Fin 2 × Bool) ≃ Fin 4)
    (e : Fin 2) (B : Kernel ℂ) : Kernel ℂ := fun a b =>
  WeightedGauge.bitWeight (r (ports (e,false))) a * B a b *
    WeightedGauge.bitWeight (r (ports (e,true))) b

/-- Tensor factors are transported in the SAME literal endpoint order. -/
theorem gauge_pairTensor (r : Fin 4 → ℂ) (ports : (Fin 2 × Bool) ≃ Fin 4)
    (B C : Kernel ℂ) :
    WeightedGauge.gauge r (pairTensor ports B C)=
      pairTensor ports (portBinary r ports 0 B) (portBinary r ports 1 C) := by
  funext x
  change (∏ i,WeightedGauge.bitWeight (r i) (x i))*
      (B (x (ports (0,false))) (x (ports (0,true))) *
        C (x (ports (1,false))) (x (ports (1,true)))) = _
  rw [←ports.prod_comp (fun i => WeightedGauge.bitWeight (r i) (x i)),Fintype.prod_prod_type]
  simp only [Fin.prod_univ_two,Fintype.prod_bool,pairTensor,portBinary]
  ring

theorem erase_root {m : ℕ} {B : Kernel ℂ} (rooted : IsRootMonomial m B) : IsRootMonomial 0 B := by
  rcases rooted with ⟨h01,h10,h00,h11,_⟩ | ⟨h00,h11,h01,h10,_⟩
  · exact Or.inl ⟨h01,h10,h00,h11,by simp⟩
  · exact Or.inr ⟨h00,h11,h01,h10,by simp⟩

theorem portBinary_monomial (r : Fin 4 → ℂ) (nonzero : ∀ i,r i≠0)
    (ports : (Fin 2 × Bool) ≃ Fin 4) (e : Fin 2) (B : Kernel ℂ)
    (monomial : IsRootMonomial 0 B) : IsRootMonomial 0 (portBinary r ports e B) := by
  have first := nonzero (ports (e,false))
  have second := nonzero (ports (e,true))
  rcases monomial with ⟨h01,h10,h00,h11,_⟩ | ⟨h00,h11,h01,h10,_⟩
  · left
    refine ⟨?_,?_,?_,?_,by simp⟩
    · simp [portBinary,h01]
    · simp [portBinary,h10]
    · simpa only [portBinary,WeightedGauge.bitWeight_false,one_mul,mul_one] using h00
    · simpa only [portBinary,WeightedGauge.bitWeight_true] using mul_ne_zero (mul_ne_zero first h11) second
  · right
    refine ⟨?_,?_,?_,?_,by simp⟩
    · simp [portBinary,h00]
    · simp [portBinary,h11]
    · simpa only [portBinary,WeightedGauge.bitWeight_false,WeightedGauge.bitWeight_true,one_mul] using
        mul_ne_zero h01 second
    · simpa only [portBinary,WeightedGauge.bitWeight_false,WeightedGauge.bitWeight_true,mul_one] using
        mul_ne_zero first h10

/-- A nonzero diagonal gauge preserves the actual complementary singleton
axes, with the precise individual coefficient correction displayed. -/
theorem portBinary_axis (r : Fin 4 → ℂ) (ports : (Fin 2 × Bool) ≃ Fin 4)
    (e : Fin 2) (p o : Bool) (c : ℂ) :
    portBinary r ports e (c • parityAxis p o)=
      (WeightedGauge.bitWeight (r (ports (e,false))) o*c*
        WeightedGauge.bitWeight (r (ports (e,true))) (o^^p)) • parityAxis p o := by
  funext a b
  cases p <;> cases o <;> cases a <;> cases b <;>
    simp [portBinary,parityAxis,WeightedGauge.bitWeight] <;> ring

structure Complementary (U V : Signature ℂ 4) where
  ports : (Fin 2 × Bool) ≃ Fin 4
  fixed : Kernel ℂ
  monomial : IsRootMonomial 0 fixed
  parity : Bool
  orientation : Bool
  coefficient : Bool → ℂ
  nonzero : ∀ a,coefficient a≠0
  endpoint : ∀ a,(if a then V else U)=pairTensor ports fixed
    (coefficient a • parityAxis parity (orientation^^a))

/-- Full coefficient/port transport of the SAME complementary payload back
to the original two endpoints. No shared even/odd gauge is required. -/
def complementaryInverse {m : ℕ} (r : Fin 4 → Scalar) (nonzero : ∀ i,r i≠0)
    (U V : Signature Scalar 4)
    (C : ClosureRootPencil.Complementary m
      (complexTensor (WeightedGauge.gauge r U)) (complexTensor (WeightedGauge.gauge r V))) :
    Complementary (complexTensor U) (complexTensor V) := by
  let s : Fin 4 → ℂ := fun i => (complexWeights r i)⁻¹
  have hs : ∀ i,s i≠0 := fun i => inv_ne_zero (complexWeights_nonzero r nonzero i)
  let coefficient := fun a : Bool =>
    WeightedGauge.bitWeight (s (C.ruling.ports (1,false))) (C.orientation^^a) * C.coefficient a *
      WeightedGauge.bitWeight (s (C.ruling.ports (1,true))) ((C.orientation^^a)^^C.parity)
  refine {
    ports := C.ruling.ports
    fixed := portBinary s C.ruling.ports 0 C.ruling.fixed
    monomial := portBinary_monomial s hs _ _ _ (erase_root C.ruling.fixedRoot)
    parity := C.parity
    orientation := C.orientation
    coefficient := coefficient
    nonzero := ?_
    endpoint := ?_ }
  · intro a
    exact mul_ne_zero (mul_ne_zero
      (WeightedGauge.bitWeight_ne_zero (hs _) _) (C.coefficient_nonzero a))
      (WeightedGauge.bitWeight_ne_zero (hs _) _)
  · intro a
    have image := congrArg (WeightedGauge.gauge s) (C.endpoint a)
    rw [gauge_pairTensor,portBinary_axis] at image
    cases a
    · simpa only [Bool.false_eq_true,ite_false,Bool.xor_false,
        complex_gauge_inverse r nonzero U,s,coefficient] using image
    · simpa only [ite_true,Bool.xor_true,
        complex_gauge_inverse r nonzero V,s,coefficient] using image

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureWeightedPencil
