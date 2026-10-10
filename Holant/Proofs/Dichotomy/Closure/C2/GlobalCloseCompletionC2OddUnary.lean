import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2OddDescent
import Holant.Proofs.Dichotomy.Closure.Stop.GlobalCloseCompletionStopUnaryCurrent
import Holant.Proofs.Closure.ProgrammeSaturation

/-! Any actual nonzero odd source produces an actual nonzero unary by finite
raw-card descent. Its full factor catalogue is installed by the existing real
source programme, preserving every old row, and the exact current unary
source pipeline is invoked. No unary hardness conclusion is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OddUnary
open Holant Holant.Tractable Holant.Algebraic Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Projective.BoundedTorsion
namespace U
export GlobalCloseCompletionStopUnaryCurrent (Completion complete)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K] [NumberField K]
variable (F : SignatureFamily K) (torsion : ResidualTorsion F) (hI : RetainsIdentity F)

include torsion hI in
theorem actual_unary {n : ℕ} (f : Signature K n) (actual : Gadget.Realizes F .disequality f)
    (nonzero : f≠0) (odd : Odd n) :
    ∃u : Signature K 1,u≠0 ∧ Gadget.Realizes F .disequality u := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases one : n=1
    · subst n
      exact ⟨f,nonzero,actual⟩
    have three : 3≤n := by obtain ⟨k,hk⟩ := odd;omega
    obtain ⟨m,rfl⟩ : ∃m,n=m+3 := ⟨n-3,by omega⟩
    obtain ⟨key,live⟩ := GlobalCloseCompletionC2OddDescent.raw_live F torsion hI f nonzero
    apply ih (m+1) (by omega) (rawCard F torsion f key)
      (rawCard_realizes_exact F torsion hI (by norm_num) f actual key) live
    obtain ⟨k,hk⟩ := odd
    exact ⟨k-1,by omega⟩

variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
variable (tau : ResidualTorsion P.family) (identity : RetainsIdentity P.family)
variable {n : ℕ} (f : Signature (OI.K G) n) (actual : Gadget.Realizes P.family .disequality f)
variable (nonzero : f≠0) (odd : Odd n)

def unary : Signature (OI.K G) 1 := (actual_unary P.family tau identity f actual nonzero odd).choose
theorem unary_nonzero : unary G P tau identity f actual nonzero odd≠0 :=
  (actual_unary P.family tau identity f actual nonzero odd).choose_spec.1
theorem unary_actual : Gadget.Realizes P.family .disequality (unary G P tau identity f actual nonzero odd) :=
  (actual_unary P.family tau identity f actual nonzero odd).choose_spec.2

abbrev signature : AnySignature (OI.K G) := ⟨1,unary G P tau identity f actual nonzero odd⟩
abbrev palette : Palette G := ProgrammeSaturation.palette G P
  (signature G P tau identity f actual nonzero odd) (unary_nonzero G P tau identity f actual nonzero odd)
  (by change 0<1;decide) (unary_actual G P tau identity f actual nonzero odd)

theorem retains_old : P.family⊆(palette G P tau identity f actual nonzero odd).family :=
  ProgrammeSaturation.retains_old G P _ _ _ _

theorem retained : (signature G P tau identity f actual nonzero odd)∈
    (palette G P tau identity f actual nonzero odd).family := by
  exact ⟨RetainedFactorCatalogue.rootLabel G P _ _,
    congrArg Sigma.fst (ProgrammeSaturation.root_saved G P _ _ _ _)⟩

def source : U.Completion G (palette G P tau identity f actual nonzero odd)
    (unary G P tau identity f actual nonzero odd) (retained G P tau identity f actual nonzero odd) :=
  U.complete G (palette G P tau identity f actual nonzero odd)
    (unary G P tau identity f actual nonzero odd) (retained G P tau identity f actual nonzero odd)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2OddUnary
end
