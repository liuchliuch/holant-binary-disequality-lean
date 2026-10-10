import Holant.Certificates.PlatonicAtlas.DomainAtlas
import Holant.Certificates.PlatonicAtlas.Orbits
import Holant.Certificates.PlatonicAtlas.LineGraphs
import Holant.Certificates.PlatonicAtlas.MarkedDisplays
import Holant.Certificates.PlatonicAtlas.SourceHistograms
import Holant.Certificates.PlatonicIncidence.SourceInterface

/-! Full Proposition A.19, Exact Platonic incidence atlas, paper1.tex
17577–17843. All finite catalogs are identified with complete intersections
of actual complex spans. The additional atlas clauses are derived here from
literal group actions, exact finite certificates, and the intrinsic complex
quotient, while the shared rich-deck and kernel-deletion clauses consume A.20.
Analytic marked similarities remain separate from actual native-X resources. -/
namespace Holant.Certificates.PlatonicAtlas
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

 def SourceDomainAtlas : Prop :=
  (∀g,(domainPoints g).card=size g) ∧
  (∀g (e : PlatonicIncidence.Mat ≃ₗ[ℂ] PlatonicIncidence.Mat),
    (projectiveDictionary (fun i => e (representative g i)) (transformed_representative_nonzero g e)).card=size g) ∧
  (projectiveDictionary External.representative External.representative_ne_zero).card=12 ∧
  (∀g S,S∈domainLines g ↔ DomainSecant g S) ∧
  ((domainLines .tetrahedral).filter (fun S => S.card=2)).card=18 ∧
  ((domainLines .tetrahedral).filter (fun S => S.card=3)).card=16 ∧
  ((domainLines .octahedral).filter (fun S => S.card=2)).card=72 ∧
  ((domainLines .octahedral).filter (fun S => S.card=3)).card=32 ∧
  ((domainLines .octahedral).filter (fun S => S.card=4)).card=18 ∧
  ((domainLines .icosahedral).filter (fun S => S.card=2)).card=450 ∧
  ((domainLines .icosahedral).filter (fun S => S.card=3)).card=200 ∧
  ((domainLines .icosahedral).filter (fun S => S.card=5)).card=72 ∧
  (deck .tetrahedral).card=432 ∧ (deck .octahedral).card=1728 ∧
  External.deck.card=432 ∧ (deck .icosahedral).card=10800 ∧
  (∀f : OctahedralSeparator.Form,(markedDeck f).card=1728)

 theorem source_domain_atlas : SourceDomainAtlas :=
  ⟨domainPoints_card,transformed_domain_points_card,external_domain_points_card,domainLines_exact,tetrahedral_domain_counts.1,tetrahedral_domain_counts.2.1,
    octahedral_domain_counts.1,octahedral_domain_counts.2.1,octahedral_domain_counts.2.2.1,
    icosahedral_domain_counts.1,icosahedral_domain_counts.2.1,icosahedral_domain_counts.2.2.2,
    standard_deck_counts.1,standard_deck_counts.2.1,External.deck_card,standard_deck_counts.2.2,
    markedDeck_card⟩

 def SourcePointIncidences : Prop :=
  (∀i : Fin 12,{S : Finset (Fin 12) | DomainSecant .tetrahedral S ∧ i∈S ∧ S.card=3}.ncard=4) ∧
  (∀i : Fin 24,{S : Finset (Fin 24) | DomainSecant .octahedral S ∧ i∈S ∧ S.card=3}.ncard=4 ∧
    {S : Finset (Fin 24) | DomainSecant .octahedral S ∧ i∈S ∧ S.card=4}.ncard=3) ∧
  (∀i : Fin 60,{S : Finset (Fin 60) | DomainSecant .icosahedral S ∧ i∈S ∧ S.card=3}.ncard=10 ∧
    {S : Finset (Fin 60) | DomainSecant .icosahedral S ∧ i∈S ∧ S.card=5}.ncard=6)

 theorem source_point_incidences : SourcePointIncidences := by
  refine ⟨?_,?_,?_⟩
  · intro i
    exact (actual_linesThrough_card .tetrahedral i 3).trans (tetrahedral_point_incidences i)
  · intro i
    exact ⟨(actual_linesThrough_card .octahedral i 3).trans (octahedral_point_incidences i).1,
      (actual_linesThrough_card .octahedral i 4).trans (octahedral_point_incidences i).2⟩
  · intro i
    exact ⟨(actual_linesThrough_card .icosahedral i 3).trans (icosahedral_point_incidences i).1,
      (actual_linesThrough_card .icosahedral i 5).trans (icosahedral_point_incidences i).2⟩

 def SourceDomainOrbits : Prop :=
  ∀g S,DomainSecant g S → ∃U V : PlatonicIncidence.Mat,groupDirection g U ∧ groupDirection g V ∧
    ∀k : Fin (size g),k∈S ↔ ∃j∈baseLine g (seed g S.card),
      Proportional (representative g k) (U*representative g j*V)

 def SourceIntersectionGraphs : Prop :=
  ∀g,(actualLineGraph g).Connected ∧ (actualLineGraph g).edgeSet.ncard=
    match g with | .tetrahedral => 72 | .octahedral => 504 | .icosahedral => 7200

 def SourceAllDeletions : Prop :=
  ∀g (e : PlatonicIncidence.Mat ≃ₗ[ℂ] PlatonicIncidence.Mat),
    {S : Finset (Fin (size g)) | ∃W : Submodule ℂ PlatonicIncidence.Mat,Module.finrank ℂ W≤2 ∧
      ∀i : Fin (size g),i∈S ↔ e (representative g i)∈W}.ncard=1+size g+secantCount g

 def SourceSpanningKernels : Prop :=
  Submodule.span ℂ (Set.range sourceAxes)=⊤ ∧
  (∀g i,groupDirection g (sourceAxes i)) ∧
  (∀f i,OctahedralSeparator.Direction f (thetaEquiv f (sourceAxes i))) ∧
  (∀f,Submodule.span ℂ (Set.range (fun i => thetaEquiv f (sourceAxes i)))=⊤) ∧
  (∀i,External.Direction (externalAxes i)) ∧ Submodule.span ℂ (Set.range externalAxes)=⊤

 def SourceMarkedDisplays : Prop :=
  (∀(U V : BinaryMatrix),act (markLegs 1) (P0 U V)=P0 (OctahedralSeparator.complexTheta 1 U) (OctahedralSeparator.complexTheta 1 V)) ∧
  (∀(U V : BinaryMatrix),Proportional (act (markLegs 1) (P1 U V))
    (P1 (OctahedralSeparator.complexTheta 1 (U*physicalX)) (OctahedralSeparator.complexTheta 1 (physicalX*V)))) ∧
  (∀(U V : BinaryMatrix),Proportional (act (markLegs 1) (P2 U V))
    (P2 (OctahedralSeparator.complexTheta 1 U) (OctahedralSeparator.complexTheta 1 (physicalX*V*physicalX)))) ∧
  (∀g (e : PlatonicIncidence.Mat ≃ₗ[ℂ] PlatonicIncidence.Mat) S,
    MatrixSecant (fun i => e (representative g i)) S ↔ DomainSecant g S) ∧
  (∀f L,GroupLegs .octahedral L → ∀j,OctahedralSeparator.Direction f (currentLegs f L j)) ∧
  (∀f L F,act (currentLegs f L) (act (markLegs f) F)=act (markLegs f) (act L F))

 theorem source_marked_displays : SourceMarkedDisplays :=
  ⟨prime_transport_P0,prime_transport_P1,prime_transport_P2,
    fun g e S => matrixSecant_transport e (representative g) S,currentLegs_mem,currentLegs_intertwine⟩

 def SourceExternalAction : Prop :=
  (∀p q : {p : Point // p∈External.deck},∃γ : Equiv.Perm {p : Point // p∈External.deck},
    γ∈externalGamma ∧ γ p=q) ∧
  (∀F j i,Gadget.Realizes (physicalFamily F {U | External.Direction U}) .disequality
    (act (physicalSingleLeg j (External.representative i)) F)) ∧
  (∀j r U V,External.Direction U → External.Direction V →
    ∃S T,External.Direction S ∧ External.Direction T ∧
      Tensor.reindex (adjacent j) (matchingTensor r U V)=matchingTensor (adjacentLabels j r) S T)

 theorem source_external_action : SourceExternalAction :=
  ⟨externalGamma_transitive,external_generators_physical,
    fun j r U V hU hV => adjacent_matching External.Direction External.Direction.transpose j r U V hU hV⟩

/-- Intrinsic quotient geometry in every complex vector space, with arbitrary
nonzero representatives of both the base and the other point. -/
 def SourceQuotientGeometry : Prop :=
  ∀(V : Type) [AddCommGroup V] [Module ℂ V],
    (∀(p q r : Projectivization ℂ V) (hq : q≠p) (hr : r≠p),
      quotientDirection p q hq=quotientDirection p r hr ↔ Projectivization.IsCollinear {p,q,r}) ∧
    (∀(p : Projectivization ℂ V) (u : V) (hu : u≠0) (hup : Projectivization.mk ℂ u hu=p),
      Submodule.span ℂ ({u} : Set V)=p.submodule) ∧
    (∀(p q : Projectivization ℂ V) (hq : q≠p) (v : V) (hv : v≠0)
      (hvq : Projectivization.mk ℂ v hv=q),quotientDirection p q hq=
        Projectivization.mk ℂ (p.submodule.mkQ v) (quotient_representative_ne_zero p q hq v hv hvq))

 theorem source_quotient_geometry : SourceQuotientGeometry :=
  fun _ _ _ => ⟨quotientDirection_eq_iff_isCollinear,span_representative_eq_point_submodule,quotientDirection_eq_mk⟩

 def SourceQuotientHistograms : Prop :=
  (∀n,quotientMultiplicity External.deck (External.deckPoint (0,0,0)) n=
    if n=1 then 415 else if n=2 then 8 else 0) ∧
  (∀n,quotientMultiplicity (deck .octahedral) (basePoint 0) n=
    if n=1 then 1645 else if n=2 then 32 else if n=3 then 6 else 0) ∧
  (∀n,quotientMultiplicity (deck .icosahedral) (basePoint 0) n=
    if n=1 then 10591 else if n=2 then 80 else if n=4 then 12 else 0)

/-- Every source clause of A.19, with generic quotient representative
independence supplied by quotientDirection_eq_mk_representatives and actual
spectrum multiplicity by quotientMultiplicity_spectrum. The A.20 conjuncts
retain stronger opposite-I and arbitrary analytic-dictionary clauses. -/
 theorem source_A19 : SourceDomainAtlas ∧ SourceCountTable ∧ SourceLineCompleteness ∧
    SourcePointIncidences ∧ SourceDomainOrbits ∧ SourceIntersectionGraphs ∧
    SourceAllDeletions ∧ SourceKernelDeletion ∧ SourceSpanningKernels ∧
    SourceMarkedDisplays ∧ SourcePhysicalWitnesses ∧ SourceExternalAction ∧ SourceQuotientGeometry ∧ SourceQuotientHistograms :=
  ⟨source_domain_atlas,source_A20.1,source_A20.2.1,source_point_incidences,actual_left_right_orbit,
    fun g => ⟨actualLineGraph_connected g,actualLineGraph_edge_count g⟩,
    transformed_deletion_count,source_A20.2.2.2,
    ⟨sourceAxes_span,sourceAxes_actual,marked_sourceAxes_actual,marked_sourceAxes_span,externalAxes_actual,externalAxes_span⟩,
    source_marked_displays,source_A20.2.2.1,source_external_action,source_quotient_geometry,
    ⟨external_quotient_histogram,octahedral_quotient_histogram,icosahedral_quotient_histogram⟩⟩

end
end Holant.Certificates.PlatonicAtlas
