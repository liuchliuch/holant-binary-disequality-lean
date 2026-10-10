import Holant.Proofs.AlgebraicRecognition.EncodedSystem
import Holant.Proofs.Algorithms.TransformRecognition.SymbolicTransform
import Mathlib.Logic.Equiv.Fin.Basic


namespace Holant.LocalDrafts.EffectiveAlgebraic.MatrixWitness
open Holant Holant.Tractable PowerArithmetic
open Holant.LocalDrafts.MainChain.TransformRecognition

abbrev Candidate (d k : ℕ) := Fin (5 + k) → Vector d

/-- Computational adapter for the index in the read-only symbolic module. -/
def index (u v : Bool) : Fin 5 :=
  if u then (if v then 3 else 2) else (if v then 1 else 0)

def matrixCode {d k : ℕ} (x : Candidate d k) (u v : Bool) : Vector d :=
  x (Fin.castAdd k (index u v))

def determinantCode {d k : ℕ} (c : Vector d) (x : Candidate d k) : Vector d :=
  (data c).mulCode (matrixCode x false false) (matrixCode x true true) -
    (data c).mulCode (matrixCode x false true) (matrixCode x true false)

def inverseCode {d k : ℕ} (c : Vector d) (x : Candidate d k) (u v : Bool) : Vector d :=
  (data c).mulCode (x (Fin.castAdd k 4))
    (if u = v then matrixCode x (!u) (!v) else -matrixCode x u v)

def checkGuard {d k : ℕ} (c : Vector d) (x : Candidate d k) : Bool :=
  CommonFieldCheck.zero
    ((data c).mulCode (x (Fin.castAdd k 4)) (determinantCode c x) - (data c).unitCode)

structure Output (d k : ℕ) where
  matrix : Bool → Bool → Vector d
  inverse : Bool → Bool → Vector d
  scalars : Fin k → Vector d

def output {d k : ℕ} (c : Vector d) (x : Candidate d k) : Output d k :=
  ⟨matrixCode x, inverseCode c x, fun i => x (Fin.natAdd 5 i)⟩

def extract {d k : ℕ} (c : Vector d) (x : Candidate d k) : Option (Output d k) :=
  if checkGuard c x then some (output c x) else none

/-- Original coefficients, all displayed equations, and the single matrix guard
are checked together. Validity of the proposed primitive-root descriptor itself
must still be established; this function is not a root-validity test. -/
def checkCandidate {d m k : ℕ} (c : Vector d) (source : RationalBox)
    (expression : Fin m → RationalPolynomialCode) (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5 + k)) (x : Candidate d k) : Bool :=
  EncodedSystem.check c source expression target S x && checkGuard c x

def extractCandidate {d m k : ℕ} (c : Vector d) (source : RationalBox)
    (expression : Fin m → RationalPolynomialCode) (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5 + k)) (x : Candidate d k) : Option (Output d k) :=
  if checkCandidate c source expression target S x then some (output c x) else none

noncomputable def values {d k : ℕ} (θ : AlgebraicComplex) (x : Candidate d k) :
    SymbolicTransform.Variables (Fin k) → AlgebraicComplex :=
  fun i => decode (K := AlgebraicComplex) θ (x (finSumFinEquiv i))

theorem decode_matrix {d k : ℕ} (θ : AlgebraicComplex) (x : Candidate d k) (u v : Bool) :
    decode (K := AlgebraicComplex) θ (matrixCode x u v) =
      SymbolicTransform.matrix (values θ x) u v := rfl

theorem decode_inverse {d k : ℕ} (θ : AlgebraicComplex) (c : Vector d)
    (x : Candidate d k) (hθ : θ ^ (d + 1) = decode (K := AlgebraicComplex) θ c) (u v : Bool) :
    decode (K := AlgebraicComplex) θ (inverseCode c x u v) =
      SymbolicTransform.inverse (values θ x) u v := by
  unfold inverseCode
  rw [PowerArithmetic.decode_mul θ c _ _ hθ]
  split_ifs with h
  · simp [SymbolicTransform.inverse, SymbolicTransform.adjugate, h, values, decode_matrix]
  · simp [SymbolicTransform.inverse, SymbolicTransform.adjugate, h, values, decode_matrix]

theorem checkGuard_sound {d k : ℕ} (θ : AlgebraicComplex) (c : Vector d)
    (x : Candidate d k) (hθ : θ ^ (d + 1) = decode (K := AlgebraicComplex) θ c)
    (h : checkGuard c x = true) :
    MvPolynomial.eval₂ (RingHom.id AlgebraicComplex) (values θ x)
      (SymbolicTransform.guard (Fin k)) = 0 := by
  have hz := CommonFieldCheck.zero_sound θ _ h
  change decode (K := AlgebraicComplex) θ ((data c).mulCode (x (Fin.castAdd k 4))
    (determinantCode c x) - (data c).unitCode) = 0 at hz
  simp only [determinantCode,map_sub,PowerArithmetic.decode_mul θ c _ _ hθ] at hz
  rw [SymbolicTransform.eval_guard]
  simpa [data, SymbolicTransform.determinant, SymbolicTransform.matrix,
    SymbolicTransform.index, values, matrixCode, index] using hz

/-- Soundness consumes the original SymbolicTransform inverse identities. -/
theorem output_inverse_identities {d k : ℕ} (θ : AlgebraicComplex) (c : Vector d)
    (x : Candidate d k) (hθ : θ ^ (d + 1) = decode (K := AlgebraicComplex) θ c)
    (h : checkGuard c x = true) :
    Kernel.mul (fun u v => decode (K := AlgebraicComplex) θ ((output c x).matrix u v))
        (fun u v => decode (K := AlgebraicComplex) θ ((output c x).inverse u v)) = Signature.equality ∧
      Kernel.mul (fun u v => decode (K := AlgebraicComplex) θ ((output c x).inverse u v))
        (fun u v => decode (K := AlgebraicComplex) θ ((output c x).matrix u v)) = Signature.equality := by
  have hi := SymbolicTransform.inverse_identities (RingHom.id AlgebraicComplex) (values θ x)
    (checkGuard_sound θ c x hθ h)
  simpa only [output, decode_matrix, decode_inverse θ c x hθ] using hi

/-- A semantic source witness for the already computed rational output. -/
noncomputable def sourceWitness {d k : ℕ} (θ : AlgebraicComplex) (c : Vector d)
    (x : Candidate d k) (hθ : θ ^ (d + 1) = decode (K := AlgebraicComplex) θ c)
    (h : checkGuard c x = true) : InvertibleKernel :=
  SymbolicTransform.toInvertible (values θ x) (checkGuard_sound θ c x hθ h)

theorem sourceWitness_matrix {d k : ℕ} (θ : AlgebraicComplex) (c : Vector d)
    (x : Candidate d k) (hθ : θ ^ (d + 1) = decode (K := AlgebraicComplex) θ c)
    (h : checkGuard c x = true) (u v : Bool) :
    (sourceWitness θ c x hθ h).matrix u v =
      decode (K := AlgebraicComplex) θ ((output c x).matrix u v) := rfl

theorem sourceWitness_vertex {d k n : ℕ} (θ : AlgebraicComplex) (c : Vector d)
    (x : Candidate d k) (hθ : θ ^ (d + 1) = decode (K := AlgebraicComplex) θ c)
    (h : checkGuard c x = true) (f : Signature AlgebraicComplex n) (y : Fin n → Bool) :
    MvPolynomial.eval₂ (RingHom.id AlgebraicComplex) (values θ x) (SymbolicTransform.vertex f y) =
      Signature.coordinateAction (fun _ => (sourceWitness θ c x hθ h).inverse) f y :=
  SymbolicTransform.selected_vertex (values θ x) (checkGuard_sound θ c x hθ h) f y

theorem sourceWitness_edge {d k : ℕ} (θ : AlgebraicComplex) (c : Vector d)
    (x : Candidate d k) (hθ : θ ^ (d + 1) = decode (K := AlgebraicComplex) θ c)
    (h : checkGuard c x = true) (E : Kernel AlgebraicComplex) (u v : Bool) :
    MvPolynomial.eval₂ (RingHom.id AlgebraicComplex) (values θ x) (SymbolicTransform.edge E u v) =
      Kernel.pullback E (sourceWitness θ c x hθ h).matrix u v :=
  SymbolicTransform.selected_edge (values θ x) (checkGuard_sound θ c x hθ h) E u v

theorem decode_coe {d : ℕ} (θ : AlgebraicComplex) (v : Vector d) :
    ((decode (K := AlgebraicComplex) θ v : AlgebraicComplex) : ℂ) =
      decode (K := ℂ) (θ : ℂ) v := by
  simp only [PowerArithmetic.decode_apply, IntermediateField.coe_sum,
    IntermediateField.coe_smul, IntermediateField.coe_pow]

/-- Every original candidate address, including its matrix and parameter
blocks, crosses the actual subtype embedding after algebraic decoding. -/
private theorem candidate_values_coe {d k : ℕ} (θ : AlgebraicComplex) (x : Candidate d k) :
    (fun i : Fin (5 + k) => ((decode (K := AlgebraicComplex) θ (x i) : AlgebraicComplex) : ℂ)) =
      (fun i : Fin (5 + k) => decode (K := ℂ) (θ : ℂ) (x i)) := by
  funext i
  exact decode_coe θ (x i)

/-- Joint soundness for the literal original coefficient family and the same
matrix output used by the existing symbolic edge/vertex compiler. -/
theorem checkCandidate_sound {d m k : ℕ} (c : Vector d) (source : RationalBox)
    (expression : Fin m → RationalPolynomialCode) (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5 + k)) (x : Candidate d k)
    (θ : AlgebraicComplex) (w : Fin m → AlgebraicComplex)
    (hθ : θ ^ (d + 1) = decode (K := AlgebraicComplex) θ c) (hsource : source.Contains (θ : ℂ))
    (htarget : ∀ i, (target i).Represents (w i : ℂ))
    (h : checkCandidate c source expression target S x = true) :
    (Kernel.mul (fun u v => decode (K := AlgebraicComplex) θ ((output c x).matrix u v))
        (fun u v => decode (K := AlgebraicComplex) θ ((output c x).inverse u v)) = Signature.equality ∧
      Kernel.mul (fun u v => decode (K := AlgebraicComplex) θ ((output c x).inverse u v))
        (fun u v => decode (K := AlgebraicComplex) θ ((output c x).matrix u v)) = Signature.equality) ∧
      ∀ e ∈ S, MvPolynomial.aeval
        (fun i => ((decode (K := AlgebraicComplex) θ (x i) : AlgebraicComplex) : ℂ))
        (EncodedSystem.polynomial (fun i => (w i : ℂ)) e) = 0 := by
  simp only [checkCandidate, Bool.and_eq_true_eq_eq_true_and_eq_true] at h
  obtain ⟨hsystem, hguard⟩ := h
  refine ⟨output_inverse_identities θ c x hθ hguard, ?_⟩
  have hθC : (θ : ℂ) ^ (d + 1) = decode (K := ℂ) (θ : ℂ) c := by
    simpa only [IntermediateField.coe_pow, decode_coe] using
      congrArg (fun a : AlgebraicComplex => (a : ℂ)) hθ
  have he := EncodedSystem.check_sound c source expression target S x (θ : ℂ)
    (fun i => (w i : ℂ)) hθC hsource htarget hsystem
  intro e heS
  rw [candidate_values_coe]
  exact he e heS

/-- Variable-degree candidate syntax: relation coefficients, proposed primitive
root enclosure, original-coefficient expressions, and all matrix/scalar values.
No field dimension is frozen before enumeration. -/
abbrev RawCandidate (m k : ℕ) :=
  Σ d : ℕ, Vector d × (RationalBox ×
    ((Fin m → RationalPolynomialCode) × Candidate d k))

/-- This queue enumerates proposed certificates, NOT certified witnesses. -/
def rawAt (m k index : ℕ) : Option (RawCandidate m k) :=
  (tupleAt (α := RawCandidate m k) 1 index).map (fun v => v 0)

def rawThrough (m k height : ℕ) : List (RawCandidate m k) :=
  (tuplesThrough (α := RawCandidate m k) 1 height).map (fun v => v 0)

theorem rawAt_complete {m k : ℕ} (r : RawCandidate m k) :
    rawAt m k (Encodable.encode (fun _ : Fin 1 => r)) = some r := by
  simp [rawAt]

theorem rawThrough_complete {m k : ℕ} (r : RawCandidate m k) :
    r ∈ rawThrough m k (Encodable.encode (fun _ : Fin 1 => r)) := by
  apply List.mem_map.mpr
  exact ⟨fun _ : Fin 1 => r, tuplesThrough_complete _, rfl⟩

/-- Finite arithmetic precheck on a proposed variable-degree candidate.
Even `true` is insufficient to accept a witness until its primitive enclosure
has been certified. In particular, no Nat.find is wrapped around this test. -/
def precheckRaw {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5 + k)) (r : RawCandidate m k) : Bool :=
  checkCandidate r.2.1 r.2.2.1 r.2.2.2.1 target S r.2.2.2.2

end Holant.LocalDrafts.EffectiveAlgebraic.MatrixWitness
