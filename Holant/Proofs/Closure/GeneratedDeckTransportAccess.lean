import Holant.Proofs.Closure.GeneratedDeckTransportPower

/-! Complete current raw-key and zero-sentinel physical access at an unchanged
actual group. Nonzero access binds the copied old tree, exact integer label,
explicit inverse scalar and SAME constructed original-G programmes. No matching,
common-class membership or equality of old/fresh trees is inferred. -/
noncomputable section
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option maxRecDepth 100000
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedDeckTransport
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness.GeneralExtraction

private theorem anyPower_exponent {L : Type*} [Field L] {s : ℕ} {a : ℕ → ℕ}
    (T : (i : Fin s) → Signature L (a i.val)) {q r : AnySignature L}
    (literal : q = r) (M : GeneralPowerExposure.PowerMacro T q.2) :
    (castAnyPower T literal M).exponent = M.exponent := by cases literal; rfl
private theorem anyPower_scale {L : Type*} [Field L] {s : ℕ} {a : ℕ → ℕ}
    (T : (i : Fin s) → Signature L (a i.val)) {q r : AnySignature L}
    (literal : q = r) (M : GeneralPowerExposure.PowerMacro T q.2) :
    (castAnyPower T literal M).scale = M.scale := by cases literal; rfl
private theorem power_exponent {L : Type*} [Field L] {s n : ℕ} {a : ℕ → ℕ}
    {T : (i : Fin s) → Signature L (a i.val)} {q r : Signature L n}
    (literal : q = r) (M : GeneralPowerExposure.PowerMacro T q) :
    (castPower literal M).exponent = M.exponent := by cases literal; rfl
private theorem power_scale {L : Type*} [Field L] {s n : ℕ} {a : ℕ → ℕ}
    {T : (i : Fin s) → Signature L (a i.val)} {q r : Signature L n}
    (literal : q = r) (M : GeneralPowerExposure.PowerMacro T q) :
    (castPower literal M).scale = M.scale := by cases literal; rfl

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P Q : Palette G) (retains : P.family ⊆ Q.family)
variable (oldTorsion : ResidualTorsion P.family) (currentTorsion : ResidualTorsion Q.family)
variable (sameGroup : completeGroup Q.family currentTorsion = completeGroup P.family oldTorsion)
variable {m : ℕ} (f : Signature (OI.K G) (m+2))
variable (k : RawCardKey m (completeGroup Q.family currentTorsion))
variable (nonzero : rawCard Q.family currentTorsion f k ≠ 0)
variable (r : RootReceipt G P Q retains oldTorsion currentTorsion sameGroup f k nonzero)

theorem rootPower_exponent : (rootPower G P Q retains oldTorsion currentTorsion sameGroup f k nonzero r).exponent = 1 :=
  anyPower_exponent Q.table _ _
theorem rootPower_scale : (rootPower G P Q retains oldTorsion currentTorsion sameGroup f k nonzero r).scale = 1 :=
  anyPower_scale Q.table _ _
theorem currentRootPower_exponent :
    (currentRootPower G P Q retains oldTorsion currentTorsion sameGroup f k nonzero r).exponent = 1 := by
  rw [currentRootPower, power_exponent]
  exact rootPower_exponent G P Q retains oldTorsion currentTorsion sameGroup f k nonzero r

/-- The exact inverse scalar is inside the ordinary physical field correction. -/
theorem currentRootPower_scale :
    (currentRootPower G P Q retains oldTorsion currentTorsion sameGroup f k nonzero r).scale =
      (currentCard G P Q retains oldTorsion currentTorsion sameGroup f k).scalar⁻¹ := by
  rw [currentRootPower, power_scale]
  change (rootPower G P Q retains oldTorsion currentTorsion sameGroup f k nonzero r).scale *
    ((currentCard G P Q retains oldTorsion currentTorsion sameGroup f k).scalar ^
      (rootPower G P Q retains oldTorsion currentTorsion sameGroup f k nonzero r).exponent)⁻¹ = _
  rw [rootPower_scale, rootPower_exponent, pow_one, one_mul]

structure NonzeroAccess : Type 1 where
  oldRoot : RootReceipt G P Q retains oldTorsion currentTorsion sameGroup f k nonzero
  power : GeneralPowerExposure.PowerMacro Q.table (rawCard Q.family currentTorsion f k)
  powerIdentity : power = currentRootPower G P Q retains oldTorsion currentTorsion sameGroup f k nonzero oldRoot
  toOriginal : RetainedBranch.ToOriginalProgramme G Q ⟨m,rawCard Q.family currentTorsion f k⟩
  toOriginalIdentity : toOriginal = RetainedBranch.toOriginal G Q _ power
  fromOriginal : RetainedBranch.FromOriginalProgramme G Q ⟨m,rawCard Q.family currentTorsion f k⟩
  fromOriginalIdentity : fromOriginal = RetainedBranch.fromOriginal G Q _

def nonzeroAccess : NonzeroAccess G P Q retains oldTorsion currentTorsion sameGroup f k nonzero :=
  let M := currentRootPower G P Q retains oldTorsion currentTorsion sameGroup f k nonzero r
  ⟨r,M,rfl,RetainedBranch.toOriginal G Q _ M,rfl,RetainedBranch.fromOriginal G Q _,rfl⟩

def NonzeroAccess.signatureAccess
    (A : NonzeroAccess G P Q retains oldTorsion currentTorsion sameGroup f k nonzero) :
    CurrentSignatureAccess G Q ⟨m,rawCard Q.family currentTorsion f k⟩ :=
  ⟨A.power,A.toOriginal,A.fromOriginal,by rw [A.toOriginalIdentity]; rfl,
    by rw [A.fromOriginalIdentity]; rfl⟩

theorem NonzeroAccess.toOriginal_controlled
    (A : NonzeroAccess G P Q retains oldTorsion currentTorsion sameGroup f k nonzero) :
    A.toOriginal.controlled = RetainedBranch.controlledToOriginal G Q _ A.power := by
  rw [A.toOriginalIdentity]
  rfl

theorem NonzeroAccess.fromOriginal_controlled
    (A : NonzeroAccess G P Q retains oldTorsion currentTorsion sameGroup f k nonzero) :
    A.fromOriginal.controlled = RetainedBranch.controlledFromOriginal G Q _ := by
  rw [A.fromOriginalIdentity]
  rfl

variable (retained : (⟨m+2,f⟩ : AnySignature (OI.K G)) ∈ P.family)

/-- Actual zero-valued raw keys do not require a saved nonzero root or tree. -/
def zeroRawAccess (zero : rawCard Q.family currentTorsion f k = 0) :
    CurrentSignatureAccess G Q ⟨m,rawCard Q.family currentTorsion f k⟩ := by
  have real : Gadget.Realizes Q.family .disequality (rawCard Q.family currentTorsion f k) := by
    rw [zero]
    exact (zeroDirect G P Q retains oldTorsion f retained).realizes
  exact currentSignatureAccess G Q _ real

/-- Separate physical access for the standalone zero sentinel. -/
def sentinelAccess : CurrentSignatureAccess G Q ⟨m, (0 : Signature (OI.K G) m)⟩ :=
  currentSignatureAccess G Q _ (zeroDirect G P Q retains oldTorsion f retained).realizes

variable (hm : 2 ≤ m)
variable (labels : Fin (OccurrenceBatch.palette G P oldTorsion f retained hm).count → Fin Q.count)
variable (saved : ∀ i, Frontier.paletteRoot G Q (labels i) =
  Frontier.paletteRoot G (OccurrenceBatch.palette G P oldTorsion f retained hm) i)

/-- Full current literal raw-key access. The nonzero branch internally restores
its copied old root; the zero branch supplies a charged graph instead. -/
def copiedRawAccess : CurrentSignatureAccess G Q ⟨m,rawCard Q.family currentTorsion f k⟩ := by
  by_cases zero : rawCard Q.family currentTorsion f k = 0
  · exact zeroRawAccess G P Q retains oldTorsion currentTorsion f k retained zero
  · let old := copiedRootReceipt G P Q retains oldTorsion currentTorsion sameGroup f retained hm labels saved k zero
    exact (nonzeroAccess G P Q retains oldTorsion currentTorsion sameGroup f k zero old).signatureAccess
      G P Q retains oldTorsion currentTorsion sameGroup f k zero

/-- Covers rawDeck's sentinel AND all actual keys, including actual zero keys.
It is separately charged Q+g access, not a claim that g is a Q table label. -/
def copiedRawDeckAccess (g : Signature (OI.K G) m) (member : g ∈ rawDeck Q.family currentTorsion f) :
    CurrentSignatureAccess G Q ⟨m,g⟩ := by
  by_cases zero : g = 0
  · subst g
    exact sentinelAccess G P Q retains oldTorsion f retained
  · have hk : ∃ key : RawCardKey m (completeGroup Q.family currentTorsion), rawCard Q.family currentTorsion f key = g := by
      rcases member with hz | hr
      · exact False.elim (zero hz)
      · exact hr
    let key := Classical.choose hk
    have keyExact := Classical.choose_spec hk
    rw [← keyExact]
    exact copiedRawAccess G P Q retains oldTorsion currentTorsion sameGroup f key retained hm labels saved

end Holant.LocalDrafts.RemoteWork.StableClosureV2.GeneratedDeckTransport
end
