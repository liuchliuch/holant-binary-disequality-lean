import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.CoordinatePrimitives
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.RationalFold


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine
open Computability Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.EffectiveAlgebraic

def embedding (c : List ℚ) (b : RationalBox) (e : RationalPolynomialCode) (t : RootCode) : Bool :=
  Coordinates.isZero (Coordinates.evalAt c (Coordinates.reduce c e) t.coefficients) &&
    (RationalBox.eval b e).inside t.rectangle

/-- Unequal family lengths reject instead of silently truncating a zip. -/
def family (c : List ℚ) (b : RationalBox) :
    List RationalPolynomialCode → List RootCode → Bool
  | [],[] => true
  | e::es,t::ts => embedding c b e t && family c b es ts
  | _,_ => false

def check (r : Request) : Bool := r.shape && family r.relation r.box r.expressions r.targets

/-- Failed shape/parsing is distinct from a well-formed rejected certificate. -/
def checkBits (bits : List Bool) : Option (List Bool) := do
  let r ← decodeRequest bits
  pure (encodingBoolBool.encode (family r.relation r.box r.expressions r.targets))

theorem embedding_ofFn {d : ℕ} (c : PowerArithmetic.Vector d) (b : RationalBox)
    (e : RationalPolynomialCode) (t : RootCode) :
    embedding (List.ofFn c) b e t = CommonFieldCheck.checkEmbedding c b e t := by
  simp only [embedding, Coordinates.reduce_ofFn, Coordinates.evalAt_ofFn,
    Coordinates.isZero_ofFn, CommonFieldCheck.checkEmbedding]

theorem family_ofFn {d m : ℕ} (c : PowerArithmetic.Vector d) (b : RationalBox)
    (e : Fin m → RationalPolynomialCode) (t : Fin m → RootCode) :
    family (List.ofFn c) b (List.ofFn e) (List.ofFn t) =
      CommonFieldCheck.checkFamily c b e t := by
  induction m with
  | zero => simp [family, CommonFieldCheck.checkFamily]
  | succ m ih =>
    rw [List.ofFn_succ (f := e), List.ofFn_succ (f := t)]
    simp only [family, embedding_ofFn, ih]
    apply Bool.eq_iff_iff.mpr
    simp [CommonFieldCheck.checkFamily, Fin.forall_fin_succ]

theorem check_fromFamily {d m : ℕ} (c : PowerArithmetic.Vector d) (b : RationalBox)
    (e : Fin m → RationalPolynomialCode) (t : Fin m → RootCode) :
    check (fromFamily c b e t) = CommonFieldCheck.checkFamily c b e t := by
  simp only [check, fromFamily_shape, Bool.true_and]
  exact family_ofFn c b e t

theorem checkBits_fromFamily {d m : ℕ} (c : PowerArithmetic.Vector d) (b : RationalBox)
    (e : Fin m → RationalPolynomialCode) (t : Fin m → RootCode) :
    checkBits (requestEncoding.encode (fromFamily c b e t)) =
      some (encodingBoolBool.encode (CommonFieldCheck.checkFamily c b e t)) := by
  simp only [checkBits, decodeRequest_encode (fromFamily_shape c b e t), Option.bind_some]
  change some (encodingBoolBool.encode (family (List.ofFn c) b (List.ofFn e) (List.ofFn t))) = _
  rw [family_ofFn]

theorem family_length_of_accept (c : List ℚ) (b : RationalBox)
    (es : List RationalPolynomialCode) (ts : List RootCode)
    (h : family c b es ts = true) : es.length = ts.length := by
  induction es generalizing ts with
  | nil => cases ts <;> simp_all [family]
  | cons e es ih =>
    cases ts with
    | nil => simp [family] at h
    | cons t ts =>
      simp only [family, Bool.and_eq_true] at h
      have ht := h.2
      simpa using congrArg Nat.succ (ih ts ht)

/-- Semantic reuse preserves the ORIGINAL target polynomial and rectangle. -/
theorem check_fromFamily_sound {d m : ℕ} (c : PowerArithmetic.Vector d) (b : RationalBox)
    (e : Fin m → RationalPolynomialCode) (t : Fin m → RootCode)
    (θ : ℂ) (w : Fin m → ℂ) (hθ : θ^(d+1) = PowerArithmetic.decode θ c)
    (hb : b.Contains θ) (ht : ∀ i, (t i).Represents (w i))
    (h : check (fromFamily c b e t) = true) :
    ∀ i, PowerArithmetic.decode θ (CommonFieldCheck.reduce c (e i)) = w i := by
  rw [check_fromFamily] at h
  exact CommonFieldCheck.checkFamily_sound c b e t θ w hθ hb ht h

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine
