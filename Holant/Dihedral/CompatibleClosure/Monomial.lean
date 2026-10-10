import Holant.Marked.Monomial
import Holant.Marked.WeightedGauge.Traces

/-! Literal source M_alpha(a) traces and fusion, with all orientation scalars.
The Boolean matrix multiplication is an actual finite contraction sum. -/
noncomputable section
namespace Holant.Dihedral.CompatibleClosure
open Holant Holant.Marked

/-- Source convention: the first ordered endpoint carries the weight. -/
def M (α : Bool) (a : Scalar) : Mat := monomial α (fun x => if x then a else 1)

def exponent (α : Bool) (a : Scalar) : Scalar := if α then a⁻¹ else a

def scalar (α : Bool) (a : Scalar) : Scalar := if α then a else 1

def trace (A B : Mat) : Scalar := ∑ x : Bool, ∑ y : Bool, A x y * B x y

theorem M_isMonomial (α : Bool) {a : Scalar} (ha : a ≠ 0) : IsMonomial (M α a) :=
  ⟨α,_,(by intro x; cases x <;> simp [ha]),rfl⟩

theorem M_mem_group {m : ℕ} (hm : 0 < m) (α : Bool) {a : Scalar} (ha : Roots m a) :
    M α a ∈ groupM m := by
  cases α
  · refine ⟨a,ha,Or.inl ⟨1,one_ne_zero,?_⟩⟩
    funext x y
    cases x <;> cases y <;> simp [M,monomial,R,Tractable.diagonalKernel,scale]
  · refine ⟨a⁻¹,ha.inv,Or.inr ⟨a,ha.ne_zero hm,?_⟩⟩
    funext x y
    cases x <;> cases y <;> simp [M,monomial,S,R,Tractable.diagonalKernel,
      Kernel.mul_apply,Signature.disequality,scale,ha.ne_zero hm]

theorem transpose_M (α : Bool) (a : Scalar) (ha : a ≠ 0) :
    Kernel.transpose (M α a) = scale (scalar α a) (M α (exponent α a)) := by
  funext u v
  cases α <;> cases u <;> cases v <;>
    simp [Kernel.transpose,M,monomial,scale,scalar,exponent,ha]

/-- Every actual saturated normalized-group matrix has the source ordered
monomial form, with an explicitly nonzero original representative scalar. -/
theorem group_M_normal_form {m : ℕ} (hm : 0 < m) {T : Mat} (hT : T ∈ groupM m) :
    ∃ α a c, Roots m a ∧ c ≠ 0 ∧ T = scale c (M α a) := by
  obtain ⟨t,ht,hT | hT⟩ := hT
  · obtain ⟨c,hc,rfl⟩ := hT
    refine ⟨false,t,c,ht,hc,?_⟩
    funext u v
    cases u <;> cases v <;> simp [scale,R,Tractable.diagonalKernel,M,monomial]
  · obtain ⟨c,hc,rfl⟩ := hT
    refine ⟨true,t⁻¹,c*t,ht.inv,mul_ne_zero hc (ht.ne_zero hm),?_⟩
    funext u v
    cases u <;> cases v <;>
      simp [scale,S,R,Tractable.diagonalKernel,Kernel.mul_apply,Signature.disequality,
        M,monomial,ht.ne_zero hm] <;> ring

theorem trace_M (α : Bool) (a t : Scalar) : trace (M α a) (M α t) = 1+a*t := by
  cases α <;> simp [trace,M,monomial] <;> ring

theorem fusion (α β : Bool) (a b : Scalar) (hb : b ≠ 0) :
    Kernel.mul (M α a) (M β b) = scale (scalar α b) (M (α ^^ β) (a * exponent α b)) := by
  funext u v
  cases α <;> cases β <;> cases u <;> cases v <;>
    simp [M,monomial,Kernel.mul_apply,scale,scalar,exponent,hb] <;> field_simp

theorem triple_fusion (α γ β : Bool) (a t b : Scalar) (ht : t ≠ 0) (hb : b ≠ 0) :
    fuse (M γ t) (M α a) (M β b) =
      scale (scalar α t * scalar (α ^^ γ) b)
        (M (α ^^ γ ^^ β) (a * exponent α t * exponent (α ^^ γ) b)) := by
  rw [fuse_eq_mul,fusion α γ a t ht,scale_mul_left,fusion (α ^^ γ) β _ b hb]
  funext u v
  simp [scale,mul_assoc]

theorem fusion_scalar_ne_zero (α γ : Bool) {t b : Scalar} (ht : t ≠ 0) (hb : b ≠ 0) :
    scalar α t * scalar (α ^^ γ) b ≠ 0 := by
  cases α <;> cases γ <;> simp [scalar,ht,hb]

theorem fusion_phase_roots {m : ℕ} (α γ : Bool) {a t b : Scalar}
    (ha : Roots m a) (ht : Roots m t) (hb : Roots m b) :
    Roots m (a * exponent α t * exponent (α ^^ γ) b) := by
  apply Roots.mul
  · apply Roots.mul ha
    cases α
    · exact ht
    · exact ht.inv
  · cases h : (α ^^ γ)
    · simpa [exponent,h] using hb
    · simpa [exponent,h] using hb.inv

/-- The actual two-bit summand has exactly one supported internal assignment. -/
theorem unique_fusion_lift (α γ β : Bool) {a t b : Scalar}
    (ha : a ≠ 0) (ht : t ≠ 0) (hb : b ≠ 0) (u v : Bool) :
    fuse (M γ t) (M α a) (M β b) u v ≠ 0 ↔
      ∃! ij : Bool × Bool, M α a u ij.1 * M γ t ij.1 ij.2 * M β b ij.2 v ≠ 0 :=
  (M_isMonomial γ ht).fuse_unique_lift (M_isMonomial α ha) (M_isMonomial β hb) u v

/-- Cross-closing carries the XOR of the two original parity discrepancies;
therefore one parity change survives a mixed pair. -/
theorem fused_parity_difference (α₀ α₁ β₀ β₁ γ : Bool) :
    ((α₀ ^^ γ ^^ β₀) ^^ (α₁ ^^ γ ^^ β₁)) = ((α₀ ^^ α₁) ^^ (β₀ ^^ β₁)) := by
  cases α₀ <;> cases α₁ <;> cases β₀ <;> cases β₁ <;> cases γ <;> decide

/-- The two sampled products may acquire different scalars; a protected
coefficient determinant on a different factor is still multiplied exactly. -/
theorem protected_determinant (c₀ c₁ a₀ b₀ a₁ b₁ : Scalar) :
    (c₀*a₀)*(c₁*b₁) - (c₀*b₀)*(c₁*a₁) =
      (c₀*c₁)*(a₀*b₁-b₀*a₁) := by ring

theorem protected_determinant_ne_zero {c₀ c₁ a₀ b₀ a₁ b₁ : Scalar}
    (hc₀ : c₀ ≠ 0) (hc₁ : c₁ ≠ 0) (h : a₀*b₁-b₀*a₁ ≠ 0) :
    (c₀*a₀)*(c₁*b₁) - (c₀*b₀)*(c₁*a₁) ≠ 0 := by
  rw [protected_determinant]
  exact mul_ne_zero (mul_ne_zero hc₀ hc₁) h

end Holant.Dihedral.CompatibleClosure
