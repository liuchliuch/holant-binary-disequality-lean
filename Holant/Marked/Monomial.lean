import Holant.Marked.Fusion
import Holant.Marked.Groups

/-! Unique internal lifts for actual Boolean monomial contractions. The result
is about the nonzero summands of the bilinear contraction, not a formal word. -/
namespace Holant.Marked
open Tractable
noncomputable section

def monomial (flip : Bool) (w : Bool → Scalar) : Mat :=
  fun a b => if b = Bool.xor a flip then w a else 0

def IsMonomial (T : Mat) : Prop :=
  ∃ flip w, (∀ a, w a ≠ 0) ∧ T = monomial flip w

theorem monomial_mul (p q : Bool) (w v : Bool → Scalar) :
    Kernel.mul (monomial p w) (monomial q v) =
      monomial (Bool.xor p q) (fun a => w a * v (Bool.xor a p)) := by
  funext a b
  cases p <;> cases q <;> cases a <;> cases b <;>
    simp [monomial, Kernel.mul_apply]

theorem monomial_transpose (p : Bool) (w : Bool → Scalar) :
    Kernel.transpose (monomial p w) = monomial p (fun a => w (Bool.xor a p)) := by
  funext a b
  cases p <;> cases a <;> cases b <;> simp [monomial, Kernel.transpose]

theorem monomial_scale (c : Scalar) (p : Bool) (w : Bool → Scalar) :
    scale c (monomial p w) = monomial p (fun a => c * w a) := by
  funext a b
  simp [monomial, scale, mul_ite]

theorem IsMonomial.mul {T V : Mat} (hT : IsMonomial T) (hV : IsMonomial V) :
    IsMonomial (Kernel.mul T V) := by
  obtain ⟨p, w, hw, rfl⟩ := hT
  obtain ⟨q, v, hv, rfl⟩ := hV
  exact ⟨Bool.xor p q, _, fun a => mul_ne_zero (hw a) (hv _), monomial_mul p q w v⟩

theorem IsMonomial.scale {T : Mat} (hT : IsMonomial T) {c : Scalar} (hc : c ≠ 0) :
    IsMonomial (scale c T) := by
  obtain ⟨p, w, hw, rfl⟩ := hT
  exact ⟨p, _, fun a => mul_ne_zero hc (hw a), monomial_scale c p w⟩

theorem IsMonomial.projective {T V : Mat} (hT : IsMonomial T)
    (hV : ProjectivelyEqual V T) : IsMonomial V := by
  obtain ⟨c, hc, rfl⟩ := hV
  exact hT.scale hc

theorem IsMonomial.transpose {T : Mat} (hT : IsMonomial T) :
    IsMonomial (Kernel.transpose T) := by
  obtain ⟨p, w, hw, rfl⟩ := hT
  exact ⟨p, _, fun a => hw _, monomial_transpose p w⟩

theorem diagonal_isMonomial {s t : Scalar} (hs : s ≠ 0) (ht : t ≠ 0) :
    IsMonomial (diagonalKernel s t) := by
  refine ⟨false, (fun a => if a then t else s), ?_, ?_⟩
  · intro a; cases a <;> assumption
  · funext a b
    cases a <;> cases b <;> simp [diagonalKernel, monomial]

theorem equality_isMonomial : IsMonomial (Signature.equality : Mat) := by
  rw [← R_one]
  exact diagonal_isMonomial one_ne_zero one_ne_zero

theorem disequality_isMonomial : IsMonomial (Signature.disequality : Mat) := by
  refine ⟨true, (fun _ => 1), fun _ => one_ne_zero, ?_⟩
  funext a b
  cases a <;> cases b <;> simp [Signature.disequality, monomial]

theorem groupM_isMonomial {m : ℕ} (hm : 0 < m) {T : Mat} (hT : T ∈ groupM m) :
    IsMonomial T := by
  obtain ⟨t, ht, h | h⟩ := hT
  · exact (diagonal_isMonomial one_ne_zero (ht.ne_zero hm)).projective h
  · exact (disequality_isMonomial.mul
      (diagonal_isMonomial one_ne_zero (ht.ne_zero hm))).projective h

/-- Exactly one summand survives when the outside endpoints are compatible. -/
theorem monomial_unique_internal_lift (p e q : Bool) (w z v : Bool → Scalar)
    (hw : ∀ a, w a ≠ 0) (hz : ∀ a, z a ≠ 0) (hv : ∀ a, v a ≠ 0)
    (a : Bool) :
    ∃! ij : Bool × Bool,
      monomial p w a ij.1 * monomial e z ij.1 ij.2 *
        monomial q v ij.2 (Bool.xor (Bool.xor (Bool.xor a p) e) q) ≠ 0 := by
  refine ⟨(Bool.xor a p, Bool.xor (Bool.xor a p) e), ?_, ?_⟩
  · simp [monomial, hw, hz, hv]
  · rintro ⟨i,j⟩ hij
    have hi : i = Bool.xor a p := by
      by_contra h
      simp [monomial, h] at hij
    have hj : j = Bool.xor i e := by
      by_contra h
      simp [monomial, h] at hij
    simp [hi, hj]

/-- An arbitrary fixed outer assignment has at most one internal lift, even
when its outside parity is unsupported. This is the cancellation-free claim. -/
theorem monomial_at_most_one_internal_lift (p e q : Bool) (w z v : Bool → Scalar)
    (a b : Bool) (ij kl : Bool × Bool)
    (hij : monomial p w a ij.1 * monomial e z ij.1 ij.2 * monomial q v ij.2 b ≠ 0)
    (hkl : monomial p w a kl.1 * monomial e z kl.1 kl.2 * monomial q v kl.2 b ≠ 0) :
    ij = kl := by
  have first (r : Bool × Bool)
      (hr : monomial p w a r.1 * monomial e z r.1 r.2 * monomial q v r.2 b ≠ 0) :
      r.1 = Bool.xor a p ∧ r.2 = Bool.xor r.1 e := by
    constructor <;> by_contra hh <;> simp [monomial, hh] at hr
  obtain ⟨hi, hj⟩ := first ij hij
  obtain ⟨hk, hl⟩ := first kl hkl
  apply Prod.ext <;> simp_all

/-- The two-bit contraction is the product of its unique surviving entries;
there is no cancellation hidden in the matrix notation. -/
theorem monomial_fuse_value (p e q : Bool) (w z v : Bool → Scalar) (a b : Bool) :
    fuse (monomial e z) (monomial p w) (monomial q v) a b =
      if b = Bool.xor (Bool.xor (Bool.xor a p) e) q then
        w a * z (Bool.xor a p) * v (Bool.xor (Bool.xor a p) e) else 0 := by
  rw [fuse_eq_mul, monomial_mul, monomial_mul]
  cases p <;> cases e <;> cases q <;> cases a <;> cases b <;> simp [monomial]

theorem IsMonomial.fuse_unique_lift {E L R : Mat}
    (hE : IsMonomial E) (hL : IsMonomial L) (hR : IsMonomial R) (a b : Bool) :
    fuse E L R a b ≠ 0 ↔ ∃! ij : Bool × Bool, L a ij.1 * E ij.1 ij.2 * R ij.2 b ≠ 0 := by
  obtain ⟨e, z, hz, rfl⟩ := hE
  obtain ⟨p, w, hw, rfl⟩ := hL
  obtain ⟨q, v, hv, rfl⟩ := hR
  constructor
  · intro h
    rw [monomial_fuse_value] at h
    have hb : b = Bool.xor (Bool.xor (Bool.xor a p) e) q := by
      by_contra hn
      exact h (ite_eq_right hn)
    subst b
    exact monomial_unique_internal_lift p e q w z v hw hz hv a
  · rintro ⟨⟨i,j⟩, h, _⟩
    have hi : i = Bool.xor a p := by
      by_contra hn
      simp [monomial, hn] at h
    have hj : j = Bool.xor i e := by
      by_contra hn
      simp [monomial, hn] at h
    have hb : b = Bool.xor j q := by
      by_contra hn
      simp [monomial, hn] at h
    simp [monomial_fuse_value, hi, hj, hb, hw, hz, hv]


theorem IsMonomial.unique_row {T : Mat} (hT : IsMonomial T) (a : Bool) :
    ∃! b : Bool, T a b ≠ 0 := by
  obtain ⟨p, w, hw, rfl⟩ := hT
  refine ⟨Bool.xor a p, by simp [monomial, hw], ?_⟩
  intro b hb
  by_contra h
  simp [monomial, h] at hb

/-- Actual support constraints on every successive row/column entry of a chain.
The list records each next endpoint bit in its original order. -/
def chainLift : List Mat → Bool → List Bool → Prop
  | [], _, [] => True
  | T :: Ts, a, b :: bs => T a b ≠ 0 ∧ chainLift Ts b bs
  | _, _, _ => False

/-- For any finite open monomial chain, its first boundary bit uniquely fixes
all following bits. Fixing the other boundary can only discard this lift. -/
theorem chain_unique_lift (Ts : List Mat) (hTs : ∀ T ∈ Ts, IsMonomial T) (a : Bool) :
    ∃! bs : List Bool, chainLift Ts a bs := by
  induction Ts generalizing a with
  | nil =>
    refine ⟨[], trivial, ?_⟩
    intro bs hbs
    cases bs <;> simp_all [chainLift]
  | cons T Ts ih =>
    obtain ⟨b, hb, hbu⟩ := (hTs T (by simp)).unique_row a
    obtain ⟨bs, hbs, hbsu⟩ := ih (fun V hV => hTs V (by simp [hV])) b
    refine ⟨b :: bs, ⟨hb, hbs⟩, ?_⟩
    intro cs hcs
    cases cs with
    | nil => exact False.elim hcs
    | cons c cs =>
      have hcb : c = b := hbu c hcs.1
      subst c
      exact congrArg (List.cons b) (hbsu cs hcs.2)

/-- The same finite chain is evaluated by actual summed matrix products. -/
def chainProduct : List Mat → Mat
  | [] => Signature.equality
  | T :: Ts => Kernel.mul T (chainProduct Ts)

theorem chainProduct_isMonomial (Ts : List Mat) (hTs : ∀ T ∈ Ts, IsMonomial T) :
    IsMonomial (chainProduct Ts) := by
  induction Ts with
  | nil => exact equality_isMonomial
  | cons T Ts ih =>
    exact (hTs T (by simp)).mul (ih (fun V hV => hTs V (by simp [hV])))

end
end Holant.Marked
