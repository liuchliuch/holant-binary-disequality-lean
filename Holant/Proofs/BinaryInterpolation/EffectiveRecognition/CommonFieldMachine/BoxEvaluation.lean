import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.PolynomialEvaluation


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.BoxEvaluation
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open UniversalPairReduction.SmoothingCompiler
open Holant.LocalDrafts.EffectiveAlgebraic
open ComplexIsolation.CertificateMachine (termEncoding polynomialEncoding)
open Holant.LocalDrafts.Tractability.AffineMachine

def sum (bs : List RationalBox) : RationalBox :=
  ⟨⟨(bs.map (fun b => b.re.center)).sum,(bs.map (fun b => b.re.radius)).sum⟩,
   ⟨(bs.map (fun b => b.im.center)).sum,(bs.map (fun b => b.im.radius)).sum⟩⟩

@[simp] theorem sum_nil : sum [] = RationalBox.point 0 := rfl
theorem sum_cons (b : RationalBox) (bs : List RationalBox) : sum (b::bs) = b.add (sum bs) := by
  simp [sum,RationalBox.add,RationalBall.add]

noncomputable def sumExecutes : Executes (framedListEncoding boxEncoding) boxEncoding sum := by
  let b := identityComputes boxEncoding
  let field {f : RationalBox → ℚ} (w : Computes boxEncoding rationalEncoding f) :=
    (Executes.ofComputes (WireLists.mapComputes boxEncoding rationalEncoding f w)).comp
      Companion.rationalSum
  let re := Executes.pair (field (BoxPrimitives.center (BoxPrimitives.real b)))
    (field (BoxPrimitives.radius (BoxPrimitives.real b)))
  let im := Executes.pair (field (BoxPrimitives.center (BoxPrimitives.imag b)))
    (field (BoxPrimitives.radius (BoxPrimitives.imag b)))
  exact Executes.recode (Executes.pair re im) id (fun _ => rfl) (fun _ => rfl)

noncomputable def power : Executes BoxPower.inputEncoding boxEncoding
    (fun p => RationalBox.power p.2 p.1) :=
  ⟨BoxPower.powerMachine,BoxPower.powerBound,BoxPower.power_outputs⟩

noncomputable def cell : Executes (pairEncoding boxEncoding termEncoding) boxEncoding
    (fun p => (RationalBox.point p.2.2).mul (RationalBox.power p.1 p.2.1)) := by
  let b := Wiring.firstComputes boxEncoding termEncoding
  let t := Wiring.secondComputes boxEncoding termEncoding
  let k := t.andThen (Wiring.firstComputes encodingNatBool rationalEncoding)
  let q := (t.andThen (Wiring.secondComputes encodingNatBool rationalEncoding)).andThen BoxPrimitives.point
  let pw := (Executes.ofComputes (pairComputes k b)).comp power
  exact (Executes.pair (Executes.ofComputes q) pw).comp (Executes.ofComputes BoxPrimitives.multiplication)

theorem eval_sum (b : RationalBox) (p : RationalPolynomialCode) :
    sum (p.map (fun t => (RationalBox.point t.2).mul (RationalBox.power b t.1))) =
      RationalBox.eval b p := by
  induction p with
  | nil => rfl
  | cons t ps ih =>
    rcases t with ⟨k,q⟩
    rw [List.map_cons,sum_cons,ih]
    rfl

noncomputable def eval : Executes (pairEncoding boxEncoding polynomialEncoding) boxEncoding
    (fun p => RationalBox.eval p.1 p.2) :=
  Executes.congr ((Executes.mapList boxEncoding termEncoding boxEncoding
    (fun b t => (RationalBox.point t.2).mul (RationalBox.power b t.1)) cell).comp sumExecutes)
    (fun p => eval_sum p.1 p.2)

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.BoxEvaluation
