import Holant.Proofs.Closure.ClosureTensorPrimeFactors
import Holant.Dihedral.CompatibleCoefficientLine.TensorFactor

/-! Literal original-port factor extraction and zero-safe four-card assembly.
The interpolation theorem consumes exact factor equations, allowing each of
the four cards to be zero. It does not construct FourProducts. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureStableFactor
open Holant Holant.Marked
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.Dihedral.CompatibleClosure Holant.Dihedral.CompatibleCoefficientLine

def pairOrder {n : ℕ} (i j : Fin (n+2)) : Equiv.Perm (Fin (n+2)) :=
  (Equiv.swap 1 ((Equiv.swap 0 i) j)).trans (Equiv.swap 0 i)

theorem pairOrder_first {n : ℕ} (i j : Fin (n+2)) (distinct : i≠j) : pairOrder i j 0=i := by
  have zeroOne : (0 : Fin (n+2)) ≠ 1 := by
    intro equal
    have h := congrArg Fin.val equal
    norm_num at h
  have transformed : (Equiv.swap 0 i) j ≠ 0 := by
    intro equal
    have h := congrArg (Equiv.swap 0 i) equal
    rw [Equiv.swap_apply_self,Equiv.swap_apply_left] at h
    exact distinct h.symm
  change (Equiv.swap 0 i) ((Equiv.swap 1 ((Equiv.swap 0 i) j)) 0)=i
  rw [Equiv.swap_apply_of_ne_of_ne zeroOne transformed.symm,Equiv.swap_apply_left]

theorem pairOrder_second {n : ℕ} (i j : Fin (n+2)) : pairOrder i j 1=j := by
  change (Equiv.swap 0 i) ((Equiv.swap 1 ((Equiv.swap 0 i) j)) 1)=j
  rw [Equiv.swap_apply_left,Equiv.swap_apply_self]

def liftResidual {n : ℕ} (u : Equiv.Perm (Fin (n+2))) : Equiv.Perm (Fin (n+4)) where
  toFun := Fin.cases 0 (Fin.cases 1 (fun j => (u j).succ.succ))
  invFun := Fin.cases 0 (Fin.cases 1 (fun j => (u.symm j).succ.succ))
  left_inv := by
    intro i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · rfl
    · rfl
    · simp
  right_inv := by
    intro i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i
    · rfl
    · rfl
    · simp

@[simp] theorem liftResidual_zero {n : ℕ} (u : Equiv.Perm (Fin (n+2))) : liftResidual u 0=0 := rfl
@[simp] theorem liftResidual_one {n : ℕ} (u : Equiv.Perm (Fin (n+2))) : liftResidual u 1=1 := rfl
@[simp] theorem liftResidual_tail {n : ℕ} (u : Equiv.Perm (Fin (n+2))) (i : Fin (n+2)) :
    liftResidual u i.succ.succ=(u i).succ.succ := rfl

theorem liftResidual_word {n : ℕ} (u : Equiv.Perm (Fin (n+2))) (a b : Bool) (x : Fin (n+2) → Bool) :
    (fun i => pair a b x ((liftResidual u).symm i))=pair a b (fun i => x (u.symm i)) := by
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) i <;> rfl

theorem close_liftResidual {n : ℕ} (u : Equiv.Perm (Fin (n+2))) (f : Signature Scalar (n+4))
    (p : Bool) (t : Scalar) :
    close p t (Tensor.reindex (liftResidual u).symm f)=Tensor.reindex u.symm (close p t f) := by
  funext x
  simp only [close,Tensor.reindex,liftResidual_word]

def complement {n k : ℕ} (ports : (Fin k × Bool) ≃ Fin (n+2))
    (A : Fin k → Mat) (coefficient : Scalar) (edge : Fin k) : Signature Scalar n := fun x =>
  coefficient * ∏ e ∈ ({edge}ᶜ : Finset (Fin k)),
    A e (pair false false x (ports (e,false))) (pair false false x (ports (e,true)))

theorem extract_first_edge {n k : ℕ} (ports : (Fin k × Bool) ≃ Fin (n+2))
    (A : Fin k → Mat) (coefficient : Scalar) (edge : Fin k)
    (first : ports (edge,false)=0) (second : ports (edge,true)=1)
    (a b : Bool) (x : Fin n → Bool) :
    productValue ports A coefficient (pair a b x)=A edge a b * complement ports A coefficient edge x := by
  have inserted : insertPair (ports (edge,false)) (ports (edge,true)) a b (pair false false x)=pair a b x := by
    rw [first,second]
    funext j
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) j
    · simp [insertPair,pair]
    · simp [insertPair,pair]
    · simp [insertPair,pair,Fin.succ_succ_ne_one]
  rw [←inserted,product_extract_edge]
  rfl

/-- A genuine projective line multiplier moves into the residual scalar.
The original whole-card coefficient and every other factor are retained. -/
theorem product_fixed_factor {n k : ℕ} (ports : (Fin k × Bool) ≃ Fin (n+2))
    (A : Fin k → Mat) (coefficient : Scalar) (edge : Fin k)
    (first : ports (edge,false)=0) (second : ports (edge,true)=1) (B : Mat)
    (line : ProjectivelyEqual (A edge) B) :
    ∃ R : Signature Scalar n, ∀ a b x, productValue ports A coefficient (pair a b x)=B a b * R x := by
  obtain ⟨c,_,equation⟩ := line
  refine ⟨c • complement ports A coefficient edge,?_⟩
  intro a b x
  rw [extract_first_edge ports A coefficient edge first second,equation]
  simp only [scale,Pi.smul_apply,smul_eq_mul]
  ring

/-- Bare zero-safe linear inversion builds the ancestor factor on its literal
ports. The four residual tensors need not be nonzero, mutually aligned, or
matching products. -/
theorem split_from_sample_factors {n : ℕ} (f : Signature Scalar (n+4)) (B : Mat)
    (t₀ t₁ : Scalar) (different : t₀≠t₁) (H : Bool × Bool → Signature Scalar n)
    (samples : ∀ i a b x, close i.1 (phase t₀ t₁ i) f (pair a b x)=B a b * H i x) :
    Nonempty (ProperSplit (⟨n+4,f⟩ : AnySignature Scalar)
      ⟨2,Tractable.kernelSignature B⟩ ⟨n+2,inverseSlices t₀ t₁ H⟩) := by
  exact ⟨ClosureTensorPrimeFactors.splitOfTensor f _ _ (factorPorts n)
    (by omega) (by omega) (tensor_factor_of_slices f B _
      (four_card_inversion t₀ t₁ different f B H samples))⟩

def reindexSplit {K : Type*} [Field K] {n : ℕ} {f : Signature K n} {a b : AnySignature K}
    (s : ProperSplit (⟨n,f⟩ : AnySignature K) a b) (order : Equiv.Perm (Fin n)) :
    ProperSplit (⟨n,Tensor.reindex order f⟩ : AnySignature K) a b where
  left_pos := s.left_pos
  right_pos := s.right_pos
  ports := s.ports.trans order
  scale := s.scale
  equation := by
    funext x
    exact congrFun s.equation (fun i => x (order i))

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureStableFactor
