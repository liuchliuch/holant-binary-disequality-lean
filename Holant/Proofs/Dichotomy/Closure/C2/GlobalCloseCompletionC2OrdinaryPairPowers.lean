import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinOrdinaryPair

/-! Exact positive ordinary pair-matrix powers. The graph, original labels,
edge count, and scalar are retained. Finite eigenratio gives a real Eq4
network; the nonperiodic interpolation consumer has a separate compiler. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryPairPowers
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace P
export GlobalCloseCompletionKleinOrdinaryPair (pair symmetric series series_denote seriesLabels series_exact series_ordinary)
end P
namespace M
export GeneralEOAffinePlaneChain (binary bitIndex)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K]

def power (N : Network K 4) : ℕ→Network K 4
  | 0 => N
  | k+1 => P.series (power N k) N

theorem power_denote (N : Network K 4) (A : Matrix (Fin 2) (Fin 2) K)
    (form : N.denote=P.pair (M.binary A)) (k : ℕ) :
    (power N k).denote=P.pair (M.binary (A^(k+1))) := by
  induction k with
  | zero => simpa only [power,Nat.zero_add,pow_one] using form
  | succ k ih =>
    rw [power,P.series_denote _ _ _ _ ih form,pow_succ A (k+1)]

section Labels
variable {s : ℕ} {b : ℕ→ℕ} (H : (i : Fin s)→Signature K (b i.val))
variable (N : Network K 4) (L : Labelling N.shape s 1 b)

def labels : (k : ℕ)→Labelling (power N k).shape s 1 b
  | 0 => L
  | k+1 => P.seriesLabels (power N k) (labels k) N L

theorem exact (input : LabelledNetwork.Exact H N L) (k : ℕ) :
    LabelledNetwork.Exact H (power N k) (labels N L k) := by
  induction k with
  | zero => exact input
  | succ k ih => exact P.series_exact H _ _ N L ih input
end Labels

theorem ordinary (N : Network K 4) (input : ∀e,N.edge e=Signature.equality) (k : ℕ) :
    ∀e,(power N k).edge e=Signature.equality := by
  induction k with
  | zero => exact input
  | succ k ih => exact P.series_ordinary _ N ih input

theorem vertices (N : Network K 4) (k : ℕ) :
    (power N k).shape.vertices=(k+1)*N.shape.vertices := by
  induction k with
  | zero => simp [power]
  | succ k ih =>
    change (power N k).shape.vertices+N.shape.vertices=(k+1+1)*N.shape.vertices
    rw [ih]
    ring

theorem edges (N : Network K 4) (k : ℕ) :
    (power N k).shape.edges=(k+1)*N.shape.edges+2*k := by
  induction k with
  | zero => simp [power]
  | succ k ih =>
    change ((power N k).shape.edges+N.shape.edges)+1+1=(k+1+1)*N.shape.edges+2*(k+1)
    rw [ih]
    ring

variable [CharZero K]

theorem symmetric_power (a d : K) (n : ℕ) :
    P.symmetric a d ^ n = P.symmetric (((a+d)^n+(a-d)^n)/2) (((a+d)^n-(a-d)^n)/2) := by
  induction n with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [P.symmetric,Matrix.one_apply]
  | succ n ih =>
    rw [pow_succ,ih]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P.symmetric,Matrix.mul_apply,Fin.sum_univ_two,pow_succ] <;> ring

theorem equal_eigenpowers (a d : K) (n : ℕ) (equal : (a-d)^n=(a+d)^n) :
    P.symmetric a d ^ n = (a+d)^n • (1 : Matrix (Fin 2) (Fin 2) K) := by
  rw [symmetric_power,equal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P.symmetric,Matrix.one_apply] <;> ring

theorem pair_identity (c : K) :
    P.pair (M.binary (c • (1 : Matrix (Fin 2) (Fin 2) K)))=c • Holant.EightVertex.ProductAnchor.equalityFour := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [P.pair,M.binary,M.bitIndex,Matrix.one_apply,Holant.EightVertex.ProductAnchor.equalityFour,
      Fin.forall_fin_succ,h0,h1,h2,h3]

theorem period_denote (N : Network K 4) (a d : K)
    (form : N.denote=P.pair (M.binary (P.symmetric a d)))
    (mu : a+d≠0) (t : ℕ) (positive : 0<t) (period : ((a-d)/(a+d))^t=1) :
    (power N (t-1)).denote=(a+d)^t • Holant.EightVertex.ProductAnchor.equalityFour := by
  have ht : t-1+1=t := by omega
  have eqpowers : (a-d)^t=(a+d)^t := by
    rw [div_pow] at period
    exact (div_eq_one_iff_eq (pow_ne_zero _ mu)).mp period
  rw [power_denote N _ form,ht,equal_eigenpowers a d t eqpowers,pair_identity]

theorem plus_nonzero (a d : K) (determinant : a^2≠d^2) : a+d≠0 := by
  intro zero
  apply determinant
  linear_combination (a-d)*zero

theorem minus_nonzero (a d : K) (determinant : a^2≠d^2) : a-d≠0 := by
  intro zero
  apply determinant
  linear_combination (a+d)*zero

/-- The fourth-root residual of the literal entry ratio is an exact finite
matrix-power case; no spectral oracle or analytic eigenbasis is needed. -/
theorem fourth_residual_period (a d : K) (determinant : a^2≠d^2) (fourth : d^4=a^4) :
    ((a-d)/(a+d))^4=1 := by
  have product : (a^2-d^2)*(a^2+d^2)=0 := by linear_combination -fourth
  have sum : a^2+d^2=0 := (mul_eq_zero.mp product).resolve_left (sub_ne_zero.mpr determinant)
  have powers : (a-d)^4=(a+d)^4 := by linear_combination -8*a*d*sum
  rw [div_pow,powers,div_self (pow_ne_zero _ (plus_nonzero a d determinant))]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OrdinaryPairPowers
end
