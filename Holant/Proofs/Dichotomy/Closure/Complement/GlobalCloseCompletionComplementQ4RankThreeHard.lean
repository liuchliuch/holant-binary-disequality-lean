import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4RankThreeHardField
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4Source
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ClassificationReduction
import Holant.Proofs.Dichotomy.Main.PaperControlledHardness

/-! A redundant rank-three native quaternary supplies controlled counting
hardness for its exact unchanged whole table. Support interpolation, dense EO
hardness, literal graph substitution and field codecs are all implemented. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4RankThreeHard
open Computability Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace S
export GlobalCloseCompletionComplementQ4Series (row spectrum ofSpectrum reconstruct)
end S
namespace E
export GlobalCloseCompletionComplementQ4Source (Extension rankThree)
end E
namespace D
export GlobalCloseCompletionComplementQ4ClassificationReduction (RedundantOutput)
end D
namespace R
export GlobalCloseCompletionComplementQ4RankThreeHardField (actual)
end R
namespace A
export NativeAntiTargetSource (Output base)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {s degree : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (F : FixedField K degree)

abbrev fullSix : Signature K 4:=S.row 0 1 ((2:K)⁻¹) ((2:K)⁻¹)

theorem fullSix_eo : DenseEOUnitLocal.EOSupport (fullSix (K:=K)) := by
  intro x hx
  rw [Holant.EightVertex.ProductAnchor.weight_four] at hx
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals try norm_num [h0,h1,h2,h3] at hx
  all_goals simp [fullSix,S.row,table,h0,h1,h2,h3]

theorem fullSix_dense : DenseEOUnitLocal.NonzeroMiddle (fullSix (K:=K)) := by
  norm_num [DenseEOUnitLocal.NonzeroMiddle,fullSix,S.row,entries,table]

def literalOutput (f : Signature K 4) (j : Fin s)
    (literal : (⟨a j.val,H j⟩ : AnySignature K)=⟨4,f⟩) : A.Output H 4 where
  network:=Network.corolla f
  labels:={vertex:=fun _=>j,vertex_arity:=fun _=>congrArg Sigma.fst literal,edge:=Fin.elim0}
  exact:=fun _=>literal
  native:=fun e=>Fin.elim0 e

variable {α : Type} {ea : Encoding α Bool} {f : α→ℕ}
def extension_source (E : E.Extension H F (fullSix (K:=K))) (w : SharpPWitness ea f) :
    LengthControlledOracleReduction ea encodingNatBool (RawClosedNetwork.validatedEncoding s 1 a)
      F.encoding f ((A.base H F).evaluate F) := by
  have algebra : (inferInstance : Algebra ℚ K)=DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  cases algebra
  letI : NumberField K:={to_charZero:=inferInstance,to_finiteDimensional:=F.basis.finiteDimensional_of_finite}
  let M:=literalOutput E.table fullSix E.label E.literal
  have eo : DenseEOUnitLocal.EOSupport M.network.denote:=by
    simpa only [M,literalOutput,Network.denote_corolla] using (fullSix_eo (K:=K))
  have dense : DenseEOUnitLocal.NonzeroMiddle M.network.denote:=by
    simpa only [M,literalOutput,Network.denote_corolla] using (fullSix_dense (K:=K))
  exact Programme.compose (R.actual F E.table M eo dense w) E.source

variable (O : D.RedundantOutput H) (live : O.c≠0)
/-- The complete source accepts the actual K4/redundant graph, with no
coefficient normalization or supplied identity. -/
def source (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding f ((A.base H F).evaluate F) :=
  extension_source H F
    (E.rankThree H F O.graph O.rates O.spectral O.first O.second (O.third live) O.fourth) w

include live in
theorem controlledHard : PaperControlledHardness.Hard (RawClosedNetwork.validatedEncoding s 1 a)
    F.encoding ((A.base H F).evaluate F) := by
  intro α ea f w
  exact ⟨source H F O live w⟩

variable (N : A.Output H 4) (A B C : K)
variable (form : N.network.denote=S.row A B C C) (nonzero : C≠0) (nonsingular : A^2≠B^2)
def rowSource (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) F.encoding f ((NativeAntiTargetSource.base H F).evaluate F) :=
  source H F ⟨N,A,B,C,form,nonsingular⟩ nonzero w

include form nonzero nonsingular in
theorem rowHard : PaperControlledHardness.Hard (RawClosedNetwork.validatedEncoding s 1 a)
    F.encoding ((NativeAntiTargetSource.base H F).evaluate F) :=
  controlledHard H F ⟨N,A,B,C,form,nonsingular⟩ nonzero


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4RankThreeHard
end
