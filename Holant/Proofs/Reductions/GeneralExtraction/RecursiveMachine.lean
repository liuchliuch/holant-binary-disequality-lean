import Holant.Proofs.Reductions.GeneralExtraction.RetainedPairReduction
import Holant.Proofs.Reductions.GeneralExtraction.GeneralMachineCost


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.Hardness.GeneralExtraction.RecursiveMachine
open Holant.Algebraic Holant.Complexity
open GeneralPowerExposure
variable {K : Type} [Field K] [Algebra ℚ K] {d s : ℕ} {arity : ℕ → ℕ}

inductive Chain (G : (i : Fin s) → Signature K (arity i.val)) :
    {n : ℕ} → ((i : Fin n) → Signature K (arity i.val)) → Type where
  | nil : Chain G G
  | snoc {n : ℕ} {H : (i : Fin n) → Signature K (arity i.val)}
      (previous : Chain G H) (f : Signature K (arity n)) (power : PowerMacro H f) :
      Chain G (RetainedPairReduction.extended H f)

variable (F : FixedField K d)
variable {G : (i : Fin s) → Signature K (arity i.val)}
variable {n : ℕ} {H : (i : Fin n) → Signature K (arity i.val)}

def step (f : Signature K (arity n)) (P : PowerMacro H f) :
    LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding (n+1) 1 arity) F.encoding
      (RawClosedNetwork.validatedEncoding n 1 arity) F.encoding
      ((GeneralFieldReduction.targetTables F (RetainedPairReduction.extended H f)).evaluate F)
      ((GeneralFieldReduction.targetTables F H).evaluate F) := by
  have R := GeneralFieldReduction.controlled F H f P
  rw [← funext (RetainedPairReduction.middle_value F H f)] at R
  exact R

/-- Every recursive call is an actual inlined finite machine; every endpoint
has exactly the same fixed field presentation F, without a codec equality premise. -/
def reduction : {n : ℕ} → {H : (i : Fin n) → Signature K (arity i.val)} →
    Chain G H → PolyTimeOracleReduction
      (RawClosedNetwork.validatedEncoding n 1 arity) F.encoding
      (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
      ((GeneralFieldReduction.targetTables F H).evaluate F)
      ((GeneralFieldReduction.targetTables F G).evaluate F)
  | _, _, .nil => oracleReduction_refl _ _ _
  | _, _, .snoc previous f P => (step F f P).compose (reduction previous)

def depth : {n : ℕ} → {H : (i : Fin n) → Signature K (arity i.val)} → Chain G H → ℕ
  | _, _, .nil => 0
  | _, _, .snoc previous _ _ => depth previous + 1

theorem count_depth (C : Chain G H) : n = s + depth C := by
  induction C with
  | nil => simp [depth]
  | snoc previous f P ih => simpa [depth, Nat.add_assoc] using congrArg Nat.succ ih

theorem snoc_time (C : Chain G H) (f : Signature K (arity n)) (P : PowerMacro H f) :
    (reduction F (.snoc C f P)).time =
      (step F f P).compositionTimePolynomial (reduction F C) := rfl

/-- This constructor derives both local macros from actual support, h=f⊗g,
and nonzero factors. It accepts neither a carrier nor an oracle simulation. -/
def appendTensor (C : Chain G H)
    (htwo : (2 : K) ≠ 0)
    (hs : GeneralCarrierExistence.MixedSupport
      (Set.range (fun i => (⟨arity i.val,H i⟩ : AnySignature K))))
    (f : Signature K (arity n)) (g : Signature K (arity (n+1)))
    (hm : 0 < arity n) (hn : 0 < arity (n+1)) (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : (⟨arity n + arity (n+1), Signature.tensor f g⟩ : AnySignature K) ∈
      Set.range (fun i => (⟨arity i.val,H i⟩ : AnySignature K)))
    (_hlarge : 1 < arity n ∨ 1 < arity (n+1)) :
    Chain G (RetainedPairReduction.extended (RetainedPairReduction.extended H f) g) :=
  let P := Classical.choice (GeneralPowerExposure.labelled_power H htwo hs f g hn hg hfg)
  let R := Classical.choice (RightPowerExposure.labelled_power H htwo hs f g hm hf hfg)
  .snoc (.snoc C f P) g (RetainedPairReduction.weaken H f g R)

theorem run_cost (C : Chain G H) (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
      ((GeneralFieldReduction.targetTables F G).evaluate F) oracle)
    (r : ExactSignatureTables.Input n 1 arity) :
    ∃ t ≤ (reduction F C).time.eval ((RawClosedNetwork.validatedEncoding n 1 arity).encode r).length,
      (fun c => c.bind ((reduction F C).machine.step oracle))^[t]
        (some ((reduction F C).machine.init ((RawClosedNetwork.validatedEncoding n 1 arity).encode r))) =
        some ((reduction F C).machine.output
          (F.encoding.encode ((GeneralFieldReduction.targetTables F H).evaluate F r))) ∧
      OracleBatch.primitiveCount (reduction F C).machine oracle
        ((reduction F C).machine.init ((RawClosedNetwork.validatedEncoding n 1 arity).encode r)) t ≤
        (reduction F C).machine.primitiveBudget * (reduction F C).time.eval
          ((RawClosedNetwork.validatedEncoding n 1 arity).encode r).length := by
  let run := (reduction F C).correct oracle ho r
  refine ⟨run.steps, run.steps_le_m, run.evals_in_steps, ?_⟩
  exact (OracleBatch.primitiveCount_le (reduction F C).machine oracle
    ((reduction F C).machine.init ((RawClosedNetwork.validatedEncoding n 1 arity).encode r)) run.steps).trans
      (Nat.mul_le_mul_left (reduction F C).machine.primitiveBudget run.steps_le_m)

end Holant.LocalDrafts.Hardness.GeneralExtraction.RecursiveMachine
