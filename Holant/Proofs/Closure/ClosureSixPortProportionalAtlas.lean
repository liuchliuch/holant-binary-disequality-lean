import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPP00
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPP01
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPP02
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPP10
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPP11
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPP12
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPP20
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPP21
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPP22
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPC00
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPC01
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPC02
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPC03
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPC04
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPC05
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPC10
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPC11
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPC12
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPC13
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPC14
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPC15
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPC20
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPC21
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPC22
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPC23
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPC24
import Holant.Proofs.Closure.ClosureSixPortProportionalAtlasPC25

/-! Public finite support atlas; the exact exhaustive witness trees are
partitioned by their already-enumerated residual matching coordinates. -/
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
open Holant
namespace Proportional

private theorem pp_projection_bits (ke ko : Fin 3) (ae be ao bo e0 e1 o0 o1 : Bool)
    (evenNonempty : e0=true ∨ e1=true) (oddNonempty : o0=true ∨ o1=true)
    (relation : (ae ^^ be)=(!(ao ^^ bo)))
    (doubled : (e0=true ∧ e1=true) ∨ (o0=true ∧ o1=true)) :
    ∃ i j : Fin 6, ∃ p : Bool,
      ProjectionOverflow (PPSupport ke ko ae be ao bo
        (fun z => if z then e1 else e0) (fun z => if z then o1 else o0)) i j p := by
  fin_cases ke <;> fin_cases ko
  · exact AtlasCases.pp_0_0 ae be ao bo e0 e1 o0 o1 evenNonempty oddNonempty relation doubled
  · exact AtlasCases.pp_0_1 ae be ao bo e0 e1 o0 o1 evenNonempty oddNonempty relation doubled
  · exact AtlasCases.pp_0_2 ae be ao bo e0 e1 o0 o1 evenNonempty oddNonempty relation doubled
  · exact AtlasCases.pp_1_0 ae be ao bo e0 e1 o0 o1 evenNonempty oddNonempty relation doubled
  · exact AtlasCases.pp_1_1 ae be ao bo e0 e1 o0 o1 evenNonempty oddNonempty relation doubled
  · exact AtlasCases.pp_1_2 ae be ao bo e0 e1 o0 o1 evenNonempty oddNonempty relation doubled
  · exact AtlasCases.pp_2_0 ae be ao bo e0 e1 o0 o1 evenNonempty oddNonempty relation doubled
  · exact AtlasCases.pp_2_1 ae be ao bo e0 e1 o0 o1 evenNonempty oddNonempty relation doubled
  · exact AtlasCases.pp_2_2 ae be ao bo e0 e1 o0 o1 evenNonempty oddNonempty relation doubled

/-- The 16-word and 12-word P/P configurations have a literal forbidden
endpoint-union projection. The only omitted flags are the two singleton
sectors, which share an actual fixed coordinate. -/
theorem pp_projection_overflow : ∀ ke ko : Fin 3, ∀ ae be ao bo : Bool,
    ∀ fe fo : Bool → Bool,
    (fe false=true ∨ fe true=true) → (fo false=true ∨ fo true=true) →
    (ae ^^ be)=(!(ao ^^ bo)) →
    ((fe false=true ∧ fe true=true) ∨ (fo false=true ∧ fo true=true)) →
    ∃ i j : Fin 6, ∃ p : Bool,
      ProjectionOverflow (PPSupport ke ko ae be ao bo fe fo) i j p := by
  intro ke ko ae be ao bo fe fo nonemptyE nonemptyO relation doubled
  have eDef : (fun z : Bool => if z then fe true else fe false)=fe := by funext z; cases z <;> rfl
  have oDef : (fun z : Bool => if z then fo true else fo false)=fo := by funext z; cases z <;> rfl
  have cert := pp_projection_bits ke ko ae be ao bo (fe false) (fe true) (fo false) (fo true)
    nonemptyE nonemptyO relation doubled
  simpa only [eDef,oDef] using cert


private theorem pc_projection_bits (kp : Fin 3) (edge : Fin 6)
    (ap bp f0 f1 sector a b o : Bool) (nonempty : f0=true ∨ f1=true)
    (relation : (ap ^^ bp)=(!(a ^^ b))) :
    ∃ i j : Fin 6, ∃ p : Bool,
      ProjectionCertificate (PCSupport kp ap bp (fun z => if z then f1 else f0)
        sector edge a b o) i j p := by
  fin_cases kp <;> fin_cases edge
  · exact AtlasCases.pc_0_0 ap bp f0 f1 sector a b o nonempty relation
  · exact AtlasCases.pc_0_1 ap bp f0 f1 sector a b o nonempty relation
  · exact AtlasCases.pc_0_2 ap bp f0 f1 sector a b o nonempty relation
  · exact AtlasCases.pc_0_3 ap bp f0 f1 sector a b o nonempty relation
  · exact AtlasCases.pc_0_4 ap bp f0 f1 sector a b o nonempty relation
  · exact AtlasCases.pc_0_5 ap bp f0 f1 sector a b o nonempty relation
  · exact AtlasCases.pc_1_0 ap bp f0 f1 sector a b o nonempty relation
  · exact AtlasCases.pc_1_1 ap bp f0 f1 sector a b o nonempty relation
  · exact AtlasCases.pc_1_2 ap bp f0 f1 sector a b o nonempty relation
  · exact AtlasCases.pc_1_3 ap bp f0 f1 sector a b o nonempty relation
  · exact AtlasCases.pc_1_4 ap bp f0 f1 sector a b o nonempty relation
  · exact AtlasCases.pc_1_5 ap bp f0 f1 sector a b o nonempty relation
  · exact AtlasCases.pc_2_0 ap bp f0 f1 sector a b o nonempty relation
  · exact AtlasCases.pc_2_1 ap bp f0 f1 sector a b o nonempty relation
  · exact AtlasCases.pc_2_2 ap bp f0 f1 sector a b o nonempty relation
  · exact AtlasCases.pc_2_3 ap bp f0 f1 sector a b o nonempty relation
  · exact AtlasCases.pc_2_4 ap bp f0 f1 sector a b o nonempty relation
  · exact AtlasCases.pc_2_5 ap bp f0 f1 sector a b o nonempty relation

/-- Every P/C or C/P configuration, including either vanishing proportional
endpoint, has either more than four projected words or an injective
two-word phase-one card. Both are literal root-deck obstructions. -/
theorem pc_projection_certificate : ∀ kp : Fin 3, ∀ ap bp : Bool,
    ∀ flags : Bool → Bool, ∀ sector : Bool, ∀ edge : Fin 6, ∀ a b o : Bool,
    (flags false=true ∨ flags true=true) → (ap ^^ bp)=(!(a ^^ b)) →
    ∃ i j : Fin 6, ∃ p : Bool,
      ProjectionCertificate (PCSupport kp ap bp flags sector edge a b o) i j p := by
  intro kp ap bp flags sector edge a b o nonempty relation
  have fDef : (fun z : Bool => if z then flags true else flags false)=flags := by funext z; cases z <;> rfl
  have cert := pc_projection_bits kp edge ap bp (flags false) (flags true) sector a b o nonempty relation
  simpa only [fDef] using cert

end Proportional
end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureSixPort
