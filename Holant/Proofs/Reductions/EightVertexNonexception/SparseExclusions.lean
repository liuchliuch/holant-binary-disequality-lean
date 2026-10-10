import Holant.Proofs.Reductions.EightVertexNonexception.NativeChain
import Holant.Tractable.CommonTransform


noncomputable section
namespace Holant.LocalDrafts.Hardness.EightVertexNonexception
open Holant Holant.Tractable
open scoped BigOperators

def xor3 {n : ℕ} (u v w : Fin n → Bool) : Fin n → Bool :=
  fun i => Bool.xor (Bool.xor (u i) (v i)) (w i)

theorem bitValue_xor3 (a b c : Bool) :
    bitValue (ZMod 2) (Bool.xor (Bool.xor a b) c) =
      bitValue (ZMod 2) a + bitValue (ZMod 2) b + bitValue (ZMod 2) c := by
  cases a <;> cases b <;> cases c <;> decide

theorem holds_xor3 {n : ℕ} (S : AffineSystem n) (u v w : Fin n → Bool)
    (hu : S.Holds u) (hv : S.Holds v) (hw : S.Holds w) : S.Holds (xor3 u v w) := by
  intro row
  simp only [xor3,bitValue_xor3,mul_add,Finset.sum_add_distrib]
  rw [hu row,hv row,hw row]
  have htwo : (2 : ZMod 2) = 0 := by decide
  calc
    S.rhs row + S.rhs row + S.rhs row = (2 : ZMod 2) * S.rhs row + S.rhs row := by ring
    _ = S.rhs row := by rw [htwo]; simp

theorem affine_support_xor3 {n : ℕ} {f : Signature AlgebraicComplex n}
    (hf : Affine f) (u v w : Fin n → Bool)
    (hu : f u ≠ 0) (hv : f v ≠ 0) (hw : f w ≠ 0) : f (xor3 u v w) ≠ 0 := by
  rcases hf with hzero | ⟨scale,hs,S,Q,rfl⟩
  · exact (hu (congrFun hzero u)).elim
  · have hsu : S.Holds u := by
      by_contra h
      exact hu (by simp [affineFormula,h])
    have hsv : S.Holds v := by
      by_contra h
      exact hv (by simp [affineFormula,h])
    have hsw : S.Holds w := by
      by_contra h
      exact hw (by simp [affineFormula,h])
    simpa only [affineFormula,if_pos (holds_xor3 S u v w hsu hsv hsw)] using
      mul_ne_zero hs (fourthRootPhase_ne_zero (Q.eval (xor3 u v w)))

theorem factor_support_xor3 {n : ℕ} (p : ProductFactor n) (u v w : Fin n → Bool)
    (hu : p.eval u ≠ 0) (hv : p.eval v ≠ 0) (hw : p.eval w ≠ 0) :
    p.eval (xor3 u v w) ≠ 0 := by
  cases p with
  | unary j values hnonzero =>
    change values (u j) ≠ 0 at hu
    change values (v j) ≠ 0 at hv
    change values (w j) ≠ 0 at hw
    change values (Bool.xor (Bool.xor (u j) (v j)) (w j)) ≠ 0
    cases h0 : u j <;> cases h1 : v j <;> cases h2 : w j
    all_goals simp only [h0,h1,h2] at hu hv hw ⊢
    all_goals first | exact hu | exact hv | exact hw
  | equality j k =>
    cases h0 : u j <;> cases h1 : u k <;>
      cases h2 : v j <;> cases h3 : v k <;>
      cases h4 : w j <;> cases h5 : w k <;>
      simp [ProductFactor.eval,xor3,Signature.equality,h0,h1,h2,h3,h4,h5] at hu hv hw ⊢
  | disequality j k =>
    cases h0 : u j <;> cases h1 : u k <;>
      cases h2 : v j <;> cases h3 : v k <;>
      cases h4 : w j <;> cases h5 : w k <;>
      simp [ProductFactor.eval,xor3,Signature.disequality,h0,h1,h2,h3,h4,h5] at hu hv hw ⊢

theorem productList_support_xor3 {n : ℕ} (ps : List (ProductFactor n))
    (u v w : Fin n → Bool)
    (hu : (ps.map (fun p => p.eval u)).prod ≠ 0)
    (hv : (ps.map (fun p => p.eval v)).prod ≠ 0)
    (hw : (ps.map (fun p => p.eval w)).prod ≠ 0) :
    (ps.map (fun p => p.eval (xor3 u v w))).prod ≠ 0 := by
  revert hu hv hw
  induction ps with
  | nil => intro hu hv hw; simp
  | cons p ps ih =>
    intro hu hv hw
    simp only [List.map_cons,List.prod_cons] at hu hv hw ⊢
    exact mul_ne_zero
      (factor_support_xor3 p u v w (mul_ne_zero_iff.mp hu).1
        (mul_ne_zero_iff.mp hv).1 (mul_ne_zero_iff.mp hw).1)
      (ih (mul_ne_zero_iff.mp hu).2 (mul_ne_zero_iff.mp hv).2 (mul_ne_zero_iff.mp hw).2)

theorem product_support_xor3 {n : ℕ} {f : Signature AlgebraicComplex n}
    (hf : Product f) (u v w : Fin n → Bool)
    (hu : f u ≠ 0) (hv : f v ≠ 0) (hw : f w ≠ 0) : f (xor3 u v w) ≠ 0 := by
  rcases hf with hzero | ⟨scale,hs,ps,rfl⟩
  · exact (hu (congrFun hzero u)).elim
  · change scale * (ps.map (fun p => p.eval u)).prod ≠ 0 at hu
    change scale * (ps.map (fun p => p.eval v)).prod ≠ 0 at hv
    change scale * (ps.map (fun p => p.eval w)).prod ≠ 0 at hw
    change scale * (ps.map (fun p => p.eval (xor3 u v w))).prod ≠ 0
    exact mul_ne_zero hs (productList_support_xor3 ps u v w
      (mul_ne_zero_iff.mp hu).2 (mul_ne_zero_iff.mp hv).2 (mul_ne_zero_iff.mp hw).2)

/-- These three mandatory supported words XOR to the absent 1111 word. -/
theorem mandatory_xor3 :
    xor3 ![false,false,true,true] ![false,true,false,true] ![true,false,false,true] =
      (![true,true,true,true] : Word) := by
  funext i
  fin_cases i <;> rfl

theorem sparse_not_affine (M : Signature AlgebraicComplex 4)
    (hc : NonzeroCorners M) (hs : SparseCase M) :
    ¬Affine (table (sparseEntries (entries M))) := by
  intro hf
  obtain ⟨hu,hv,hw,hz,hy⟩ := sparse_mandatory_entries M hc hs
  have h := affine_support_xor3 hf _ _ _ hu hv hw
  rw [mandatory_xor3] at h
  exact h rfl

theorem sparse_not_product (M : Signature AlgebraicComplex 4)
    (hc : NonzeroCorners M) (hs : SparseCase M) :
    ¬Product (table (sparseEntries (entries M))) := by
  intro hf
  obtain ⟨hu,hv,hw,hz,hy⟩ := sparse_mandatory_entries M hc hs
  have h := product_support_xor3 hf _ _ _ hu hv hw
  rw [mandatory_xor3] at h
  exact h rfl

theorem nativeChain_exclusions (M : Signature AlgebraicComplex 4)
    (hM : EvenSupport M) (hc : NonzeroCorners M) (hs : SparseCase M) :
    ¬Affine (nativeChain M).denote ∧ ¬Product (nativeChain M).denote := by
  rw [nativeChain_sparse M hM hs]
  exact ⟨sparse_not_affine M hc hs,sparse_not_product M hc hs⟩

end Holant.LocalDrafts.Hardness.EightVertexNonexception
