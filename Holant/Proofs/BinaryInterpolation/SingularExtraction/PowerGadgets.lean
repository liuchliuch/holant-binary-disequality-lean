import Holant.Proofs.BinaryInterpolation.SingularExtraction.PairDescent
import Holant.OpenNetworkComposition.ProjectiveSubstitution
import Holant.OpenNetworkComposition.FactorFreeNormalization.Reduction
import Holant.OneHot.NetworkBridge.FiniteNative
import Holant.Tractable.Criteria


noncomputable section
namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open Holant Holant.Tractable Holant.OpenNetworkComposition
open Holant.OpenNetworkComposition.ProjectiveSubstitution
open Holant.OpenNetworkComposition.FactorFreeNormalization

variable {K : Type*} [Field K]
set_option backward.isDefEq.respectTransparency false

/-- The exact scalar obtained by closing a cap against n copies of v by X. -/
def capValue {n : ℕ} (g : Signature K n) (v : Bool → K) : K :=
  ∑ c : Fin n → Bool, g (fun i => !(c i)) * ∏ i, v (c i)

/-- Ordered rank-one binary; there is no implicit X in this table. -/
def outerSignature (u v : Bool → K) : Signature K 2 :=
  fun x => u (x 0) * v (x 1)

def starArity (n : ℕ) : Option (Fin n) → ℕ
  | none => n
  | some _ => 2

/-- Cap ports are false edge ends, second B ports true ends, first B ports
the output. Every ordinary port occurs exactly once in this bijection. -/
def starPorts (n : ℕ) :
    (Σ j : Option (Fin n), Fin (starArity n j)) ≃ (Fin n ⊕ (Fin n × Bool)) where
  toFun p := match p with
    | ⟨none, i⟩ => .inr (i, false)
    | ⟨some j, i⟩ => if i.val = 0 then .inl j else .inr (j, true)
  invFun p := match p with
    | .inl j => ⟨some j, (0 : Fin 2)⟩
    | .inr (j, false) => ⟨none, j⟩
    | .inr (j, true) => ⟨some j, (1 : Fin 2)⟩
  left_inv p := by
    rcases p with ⟨j, i⟩
    cases j with
    | none => rfl
    | some j => fin_cases i <;> rfl
  right_inv p := by
    rcases p with j | ⟨j, b⟩
    · rfl
    · cases b <;> rfl

def star {n : ℕ} (g : Signature K n) (u v : Bool → K) :
    Holant.FiniteNetwork K (Option (Fin n)) (Fin n) n where
  arity := starArity n
  ports := starPorts n
  vertex j := match j with
    | none => g
    | some _ => outerSignature u v
  edge _ := Signature.disequality

/-- Exact assignment-sum identity for the star, including all cap entries. -/
theorem star_denote {n : ℕ} (g : Signature K n) (u v : Bool → K) :
    (star g u v).denote = fun x => capValue g v * Signature.unaryPower u n x := by
  classical
  funext x
  rw [show (star g u v).denote = _ from
    Holant.FiniteNetwork.denote_disequality (starArity n) (starPorts n) (star g u v).vertex]
  unfold Holant.FiniteNetwork.endpointChoiceDenote capValue
  rw [Finset.sum_mul]
  refine Finset.sum_congr (by ext; simp) ?_
  intro c _
  simp only [Fintype.prod_option]
  change g (fun i => !(c i)) * (∏ i : Fin n, u (x i) * v (c i)) =
    (g (fun i => !(c i)) * ∏ i, v (c i)) * Signature.unaryPower u n x
  rw [Finset.prod_mul_distrib]
  unfold Signature.unaryPower
  ac_rfl

theorem star_realizes {n : ℕ} (family : SignatureFamily K) (htwo : (2 : K) ≠ 0)
    (g : Signature K n) (u v : Bool → K)
    (hg : Gadget.RealizesUpTo family .disequality g)
    (hB : Gadget.RealizesUpTo family .disequality (outerSignature u v)) :
    Gadget.RealizesUpTo family .disequality
      (fun x => capValue g v * Signature.unaryPower u n x) := by
  rw [← star_denote]
  apply realizesUpTo_finiteNetwork family (star g u v) _ (fun _ => rfl) htwo
  intro j
  cases j with
  | none => exact hg
  | some i => exact hB

theorem power_of_cap {n : ℕ} (family : SignatureFamily K) (htwo : (2 : K) ≠ 0)
    (g : Signature K n) (u v : Bool → K)
    (hg : Gadget.RealizesUpTo family .disequality g)
    (hB : Gadget.RealizesUpTo family .disequality (outerSignature u v))
    (hc : capValue g v ≠ 0) :
    Gadget.RealizesUpTo family .disequality (Signature.unaryPower u n) := by
  obtain ⟨a, ha, H⟩ := star_realizes family htwo g u v hg hB
  refine ⟨a * capValue g v, mul_ne_zero ha hc, ?_⟩
  simpa only [mul_assoc] using H

def twoWords : (Fin 2 → Bool) ≃ (Bool × Bool) where
  toFun x := (x 0, x 1)
  invFun p := ![p.1, p.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv p := rfl

theorem native_capValue (v : Bool → K) :
    capValue (fun x : Fin 2 → Bool => Signature.disequality (x 0) (x 1)) v =
      2 * v false * v true := by
  unfold capValue
  rw [← twoWords.symm.sum_comp]
  simp [twoWords, Fintype.sum_prod_type, Fintype.sum_bool, Fin.prod_univ_succ,
    Signature.disequality]
  ring

/-- Isotropic unary caps collapse to one term; no division by an oracle
value or assertion that all other signature coefficients vanish is used. -/
theorem pin_capValue {n : ℕ} (g : Signature K n) (v : Bool → K) (p : Bool)
    (hz : v (!p) = 0) :
    capValue g v = g (fun _ => !p) * v p ^ n := by
  classical
  unfold capValue
  rw [Finset.sum_eq_single (fun _ => p)]
  · simp
  · intro x _ hx
    have hex : ∃ i, x i ≠ p := by
      by_contra hn
      push_neg at hn
      exact hx (funext hn)
    obtain ⟨i, hi⟩ := hex
    have he : x i = !p := by cases p <;> cases h : x i <;> simp_all
    have hp : (∏ j, v (x j)) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (by rw [he, hz])
    rw [hp, mul_zero]
  · simp

/-- A support-only formulation of the source two-sided hypothesis. -/
def BothSigns (family : SignatureFamily K) : Prop :=
  ∀ b : Bool, ∃ n : ℕ, ∃ f : Signature K n,
    (⟨n, f⟩ : AnySignature K) ∈ family ∧
      ∃ x, f x ≠ 0 ∧ 0 < balance b x

/-- All nonzero unary covectors have some positive-arity, actual Γ cap.
Nonisotropic unaries use the native edge; isotropic unaries use the
opposite strict support charge and the proved loop descent. -/
theorem exists_cap (family : SignatureFamily K) (htwo : (2 : K) ≠ 0)
    (hs : BothSigns family) (v : Bool → K) (hv : v ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ g : Signature K n,
      Gadget.RealizesUpTo family .disequality g ∧ capValue g v ≠ 0 := by
  by_cases h0 : v false = 0
  · have h1 : v true ≠ 0 := by
      intro h1
      apply hv
      funext b
      cases b <;> simp [h0, h1]
    obtain ⟨n, f, hmem, x, hfx, hx⟩ := hs false
    obtain ⟨m, hm, g, hg, hgv⟩ := majority_cap family htwo false f
      (Actual.of_realizes family f (Gadget.realizes_of_mem family .disequality f hmem)) x hfx hx
    refine ⟨m, hm, g, hg, ?_⟩
    rw [pin_capValue g v true h0]
    exact mul_ne_zero hgv (pow_ne_zero _ h1)
  by_cases h1 : v true = 0
  · obtain ⟨n, f, hmem, x, hfx, hx⟩ := hs true
    obtain ⟨m, hm, g, hg, hgv⟩ := majority_cap family htwo true f
      (Actual.of_realizes family f (Gadget.realizes_of_mem family .disequality f hmem)) x hfx hx
    refine ⟨m, hm, g, hg, ?_⟩
    rw [pin_capValue g v false h1]
    exact mul_ne_zero hgv (pow_ne_zero _ h0)
  refine ⟨2, by decide, (fun x => Signature.disequality (x 0) (x 1)),
    ⟨1, one_ne_zero, ?_⟩, ?_⟩
  · simpa only [EdgeKind.value, one_mul] using
      Gadget.realizes_edgeBox family EdgeKind.disequality
  · rw [native_capValue]
    exact mul_ne_zero (mul_ne_zero htwo h0) h1

theorem reverse_outer (family : SignatureFamily K) (u v : Bool → K)
    (hB : Gadget.RealizesUpTo family .disequality (outerSignature u v)) :
    Gadget.RealizesUpTo family .disequality (outerSignature v u) := by
  have h := realizesUpTo_reindex family (Equiv.swap (0 : Fin 2) 1) _ hB
  convert h using 1
  funext x
  simp [outerSignature, Tensor.reindex, mul_comm]

/-- Both tensor exponents are constructed and can differ. This is genuine
same-family physical realizability, not unary Turing access yet. -/
theorem two_unary_powers (family : SignatureFamily K) (htwo : (2 : K) ≠ 0)
    (hs : BothSigns family) (u v : Bool → K) (hu : u ≠ 0) (hv : v ≠ 0)
    (hB : Gadget.RealizesUpTo family .disequality (outerSignature u v)) :
    ∃ k l : ℕ, 0 < k ∧ 0 < l ∧
      Gadget.RealizesUpTo family .disequality (Signature.unaryPower u k) ∧
      Gadget.RealizesUpTo family .disequality (Signature.unaryPower v l) := by
  obtain ⟨k, hk, g, hg, hgv⟩ := exists_cap family htwo hs v hv
  obtain ⟨l, hl, f, hf, hfu⟩ := exists_cap family htwo hs u hu
  exact ⟨k, l, hk, hl,
    power_of_cap family htwo g u v hg hB hgv,
    power_of_cap family htwo f v u hf (reverse_outer family u v hB) hfu⟩

theorem unaryPower_noXFactor (u : Bool → K) (hu : u ≠ 0) (n : ℕ) :
    NoXFactor (Signature.unaryPower u n) := by
  obtain ⟨b, hb⟩ : ∃ b, u b ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hu (funext hn)
  rintro ⟨i, j, hij, g, hg⟩
  have h := hg (fun _ => b)
  have hn : u b ^ n ≠ 0 := pow_ne_zero _ hb
  apply hn
  simpa [Signature.unaryPower, Signature.disequality] using h

/-- Ordinary macros suitable for the existing fixed-gadget compiler.
No free identity or assumed ordinary realization is added. -/
theorem two_ordinary_powers (family : SignatureFamily K) (htwo : (2 : K) ≠ 0)
    (hs : BothSigns family) (u v : Bool → K) (hu : u ≠ 0) (hv : v ≠ 0)
    (hB : Gadget.RealizesUpTo family .disequality (outerSignature u v)) :
    ∃ k l : ℕ, 0 < k ∧ 0 < l ∧
      (∃ a : K, a ≠ 0 ∧ ∃ U : Network K k,
        (∀ w, (⟨U.shape.arity w, U.vertex w⟩ : AnySignature K) ∈ family) ∧
        (∀ e, U.edge e = Signature.disequality) ∧
        U.denote = fun x => a * Signature.unaryPower u k x) ∧
      (∃ b : K, b ≠ 0 ∧ ∃ V : Network K l,
        (∀ w, (⟨V.shape.arity w, V.vertex w⟩ : AnySignature K) ∈ family) ∧
        (∀ e, V.edge e = Signature.disequality) ∧
        V.denote = fun x => b * Signature.unaryPower v l x) := by
  obtain ⟨k, l, hk, hl, hU, hV⟩ := two_unary_powers family htwo hs u v hu hv hB
  exact ⟨k, l, hk, hl,
    realizesUpTo_exists_ordinary hU (unaryPower_noXFactor u hu k),
    realizesUpTo_exists_ordinary hV (unaryPower_noXFactor v hv l)⟩

/-- Source vocabulary join, preserving the original K-coordinate charge. -/
theorem bothSigns_of_source {family : SignatureFamily AlgebraicComplex}
    (h : Holant.Tractable.BothChargeSigns family) : BothSigns family := by
  intro b
  cases b with
  | false =>
    obtain ⟨⟨n, f⟩, hf, x, hx, hc⟩ := h.1
    exact ⟨n, f, hf, x, hx, by rw [balance_false]; omega⟩
  | true =>
    obtain ⟨⟨n, f⟩, hf, x, hx, hc⟩ := h.2
    exact ⟨n, f, hf, x, hx, by rwa [balance_true]⟩

end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
