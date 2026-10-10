import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinBResolved
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHResolved
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinChart
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinSparse

/-! Every dense standard-Klein q4 is consumed. Separating twisted squares
produce Eq4 immediately. Otherwise the derived paired-square cases become
separating in the existing H or B finite source, with exact whole-family basis
backtransfer. The actual I/J chart restores the original parity/sign cases. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinStandardDense
open Holant Holant.Tractable Holant.Algebraic Holant.Marked Holant.Marked.SupportAtlas
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal paired_squares)
end T
namespace R
export GlobalCloseCompletionKleinDenseSeparated (coverage representatives)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

private theorem swap_b_c (a b c d : AlgebraicComplex) :
    Tensor.reindex (Equiv.swap 1 2) (T.normal a b c d)=T.normal a c b d := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Tensor.reindex,T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,
      Equiv.swap_apply_def,h0,h1,h2,h3]

private theorem swap_b_d (a b c d : AlgebraicComplex) :
    Tensor.reindex (Equiv.swap 1 3) (T.normal a b c d)=T.normal a d c b := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Tensor.reindex,T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,
      Equiv.swap_apply_def,h0,h1,h2,h3]

variable {s : ℕ} {arity : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (arity i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : ClosureSourceRows.nativeKleinKind G P torsion cardinal noncyclic=.standard)

include cardinal noncyclic standard core literal in
theorem paired_classified (a b c d : AlgebraicComplex) (ha : a≠0) (hc : c≠0)
    (hab : a^2=b^2) (hcd : c^2=d^2)
    (actual : Gadget.RealizesUpTo (ClosureSourceRows.ambientFamily G P) .disequality (T.normal a b c d)) :
    GlobalCloseCompletionKleinEq4Source.CurrentTract G P ∨ GlobalCloseCompletionKleinEq4Source.Hard G := by
  obtain ⟨U,choice,A,B,C,D,form,separated⟩ :=
    GlobalCloseCompletionKleinBAlgebra.paired_separates a b c d ha hc hab hcd
  rcases choice with rfl|rfl
  · exact GlobalCloseCompletionKleinHResolved.classified G P torsion q core literal cardinal noncyclic standard
      _ actual A B C D form separated
  · exact GlobalCloseCompletionKleinBResolved.classified G P torsion cardinal noncyclic standard
      _ actual A B C D form separated

include cardinal noncyclic standard core literal in
theorem normal_classified (a b c d : AlgebraicComplex) (ha : a≠0) (hb : b≠0) (hc : c≠0) (_hd : d≠0)
    (actual : Gadget.RealizesUpTo (ClosureSourceRows.ambientFamily G P) .disequality (T.normal a b c d)) :
    GlobalCloseCompletionKleinEq4Source.CurrentTract G P ∨ GlobalCloseCompletionKleinEq4Source.Hard G := by
  classical
  by_cases h0 : (a^2-b^2)^2=(c^2-d^2)^2
  · have ac := Holant.OpenNetworkComposition.ProjectiveSubstitution.realizesUpTo_reindex
      _ (Equiv.swap 1 2) _ actual
    rw [swap_b_c] at ac
    by_cases h1 : (a^2-c^2)^2=(b^2-d^2)^2
    · have ad := Holant.OpenNetworkComposition.ProjectiveSubstitution.realizesUpTo_reindex
        _ (Equiv.swap 1 3) _ actual
      rw [swap_b_d] at ad
      by_cases h2 : (a^2-d^2)^2=(b^2-c^2)^2
      · rcases T.paired_squares a b c d h0 h1 h2 (by norm_num) with ab_cd|ac_bd|ad_bc
        · exact paired_classified G P torsion q core literal cardinal noncyclic standard
            a b c d ha hc ab_cd.1 ab_cd.2 actual
        · exact paired_classified G P torsion q core literal cardinal noncyclic standard
            a c b d ha hb ac_bd.1 ac_bd.2 ac
        · exact paired_classified G P torsion q core literal cardinal noncyclic standard
            a d c b ha hc ad_bc.1 ad_bc.2.symm ad
      · apply GlobalCloseCompletionKleinDenseSeparated.classified G P torsion cardinal noncyclic standard
          a d c b ad
        intro he
        apply h2
        calc
          _ = (c^2-b^2)^2 := he
          _ = (b^2-c^2)^2 := by ring
    · exact GlobalCloseCompletionKleinDenseSeparated.classified G P torsion cardinal noncyclic standard a c b d ac h1
  · exact GlobalCloseCompletionKleinDenseSeparated.classified G P torsion cardinal noncyclic standard a b c d actual h0

include cardinal noncyclic standard in
theorem pauli_J : Gadget.RealizesUpTo (ClosureSourceRows.ambientFamily G P) .disequality
    (kernelSignature GlobalCloseCompletionKleinChart.J) := by
  let reps := R.representatives G P torsion cardinal noncyclic standard
  refine ⟨reps.multiplier 3,reps.multiplier_ne_zero 3,?_⟩
  have h := reps.actual 3
  rw [reps.normal_form] at h
  convert h using 1
  funext x
  congr 1
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [kernelSignature,Klein.E,Klein.basisQ,Klein.matrix,GlobalCloseCompletionKleinChart.J,h0,h1]

include cardinal noncyclic standard core literal in
theorem dense_classified
    (stable : ∀f∈rawDeck P.family torsion q,Holant.Certificates.MatchingContractionClosure.MatchingOrZero (actualTransfers P.family) f)
    (p : Bool) (full : ∀x,StableCurrentEvenEOTransport.embedded G q x≠0 ↔ parity x=p) :
    GlobalCloseCompletionKleinEq4Source.CurrentTract G P ∨ GlobalCloseCompletionKleinEq4Source.Hard G := by
  have physical := ClosureSourceRows.klein_sourceDeck G P torsion .standard
    (R.coverage G P torsion cardinal noncyclic standard) q core literal stable
  obtain ⟨j,_parityRule,comp⟩ := Klein.source_standard_planes
    (R.representatives G P torsion cardinal noncyclic standard) (StableCurrentEvenEOTransport.embedded G q) physical
  have actual : Gadget.RealizesUpTo (ClosureSourceRows.ambientFamily G P) .disequality
      (StableCurrentEvenEOTransport.embedded G q) := by
    refine ⟨1,one_ne_zero,?_⟩
    simpa only [one_mul] using RingHomRealization.realizes_map (ClosureSourceRows.embedding G)
      (Gadget.realizes_of_mem _ .disequality q (literal ▸ core.retained))
  have sign : Klein.standardSign j=1 ∨ Klein.standardSign j= -1 := by
    unfold Klein.standardSign
    split_ifs <;> simp
  obtain ⟨a,b,c,d,ha,hb,hc,hd,normal⟩ := GlobalCloseCompletionKleinChart.dense_normal
    _ (StableDenseGaugeCurrent.ambient_identity G P) (pauli_J G P torsion cardinal noncyclic standard)
    _ actual p full (Klein.standardSign j) sign comp
  exact normal_classified G P torsion q core literal cardinal noncyclic standard a b c d ha hb hc hd normal

include cardinal noncyclic standard core literal in
theorem classified
    (stable : ∀f∈rawDeck P.family torsion q,Holant.Certificates.MatchingContractionClosure.MatchingOrZero (actualTransfers P.family) f) :
    GlobalCloseCompletionKleinEq4Source.CurrentTract G P ∨ GlobalCloseCompletionKleinEq4Source.Hard G := by
  classical
  by_cases dense : ∃p : Bool,∀x,StableCurrentEvenEOTransport.embedded G q x≠0 ↔ parity x=p
  · obtain ⟨p,full⟩ := dense
    exact dense_classified G P torsion q core literal cardinal noncyclic standard stable p full
  · exact GlobalCloseCompletionKleinSparse.standard_sparse_classified G P q core literal
      torsion cardinal noncyclic standard stable dense


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinStandardDense
end
