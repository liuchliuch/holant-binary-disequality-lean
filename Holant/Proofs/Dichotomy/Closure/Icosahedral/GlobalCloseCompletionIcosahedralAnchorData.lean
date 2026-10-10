import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralGoldenKeys

/-! Generic I/opposite-I coefficient proof extracted from RankThree/AnchorTables.
No old saved-State dispatcher or caller-supplied classification is imported.
This candidate retains the actual full sixty-point hypotheses and proof. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.RankThree
open Holant.Certificates Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence Holant.Certificates.MatchingProductBridge
open Holant.Certificates.TetrahedralPreservers
open scoped BigOperators

def anchorRaw (b : Fin 31) : GoldenVector := icosahedralRaw (baseAnchor .icosahedral b)

def normalRaw (b c : Fin 31) : GoldenVector :=
  let u := anchorRaw b
  let v := anchorRaw c
  ![GoldenInt.zero,
    GoldenInt.sub (GoldenInt.mul (u 2) (v 3)) (GoldenInt.mul (u 3) (v 2)),
    GoldenInt.sub (GoldenInt.mul (u 3) (v 1)) (GoldenInt.mul (u 1) (v 3)),
    GoldenInt.sub (GoldenInt.mul (u 1) (v 2)) (GoldenInt.mul (u 2) (v 1))]

def goldenDot (u v : GoldenVector) : GoldenInt :=
  GoldenInt.add
    (GoldenInt.add (GoldenInt.mul (u 0) (v 0)) (GoldenInt.mul (u 1) (v 1)))
    (GoldenInt.add (GoldenInt.mul (u 2) (v 2)) (GoldenInt.mul (u 3) (v 3)))

def planeIndices (b c : Fin 31) : Finset (Fin 60) :=
  Finset.univ.filter fun r => goldenDot (normalRaw b c) (icosahedralRaw r) = GoldenInt.zero

def projectedRaw (b c : Fin 31) (r : Fin 60) : RawProjection :=
  ![RankTwo.goldenPair (icosahedralRaw 0) (icosahedralRaw r),
    RankTwo.goldenPair (anchorRaw b) (icosahedralRaw r),
    RankTwo.goldenPair (anchorRaw c) (icosahedralRaw r)]

def zeroKey : ProjectionKey := ⟨0,fun _ => (0,0)⟩

/-- Explicit finite-coordinate equality avoids the generic function-field
DecidableEq implementation, whose logical casts do not kernel-reduce here. -/
private def projectionKeyDecidableEq (a b : ProjectionKey) : Decidable (a=b) :=
  if hp : a.pivot=b.pivot then
    if h0 : a.entries 0=b.entries 0 then
      if h1 : a.entries 1=b.entries 1 then
        if h2 : a.entries 2=b.entries 2 then
          isTrue (ProjectionKey.ext hp (funext (fun i=>by
            fin_cases i
            · exact h0
            · exact h1
            · exact h2)))
        else isFalse (fun h=>h2 (congrArg (fun k : ProjectionKey=>k.entries 2) h))
      else isFalse (fun h=>h1 (congrArg (fun k : ProjectionKey=>k.entries 1) h))
    else isFalse (fun h=>h0 (congrArg (fun k : ProjectionKey=>k.entries 0) h))
  else isFalse (fun h=>hp (congrArg ProjectionKey.pivot h))

def projectionKeys (b c : Fin 31) : Finset ProjectionKey :=
  @Finset.image (Fin 60) ProjectionKey projectionKeyDecidableEq
    (fun r => (projectionKey (projectedRaw b c r)).getD zeroKey)
    (Finset.univ.filter fun r : Fin 60 => projectionKey (projectedRaw b c r) ≠ none)

def finiteCertificate (b c : Fin 31) : Prop :=
  b=c ∨ ((planeIndices b c).card ≤ 15 ∧ 16 ≤ (projectionKeys b c).card)

instance (b c : Fin 31) : Decidable (finiteCertificate b c) := by
  unfold finiteCertificate
  infer_instance


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.RankThree
