import Holant.Certificates.PlatonicQuaternaryExits.DeficientSemantics

/-! Proposition A.26, Platonic quaternary exit certificate.

The 201 marked occurrences are an unconditional finite type: six deficient
outputs in T, O, O', and each fixed-I icosahedral display; six direct deficient
outputs in each mixed octahedral display; three reversed tetrahedral outputs;
24 octahedral frame orderings in all four forms; and30 icosahedral frames in
both displays. Repetitions of a coefficient tensor across frames are retained.
Every conclusion has a native-X graph with one original q and at most four
actual current-group binary vertices. -/
namespace Holant.Certificates.PlatonicQuaternaryExits
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

inductive SourceCase where
  | tetrahedralDeficient (p : Fin 6)
  | octahedralDeficient (f : Fin 2) (p : Fin 6)
  | icosahedralDeficient (opposite : Bool) (p : Fin 6)
  | mixedDeficient (f : Fin 2) (p : Fin 6)
  | tetrahedralReverse (s : Fin 3)
  | octahedralFrame (f : OctahedralSeparator.Form) (frame : Fin 4) (order : Fin 6)
  | icosahedralFrame (opposite : Bool) (i : Fin 30)
  deriving DecidableEq, Fintype

def SourceCase.signature : SourceCase → Signature ℂ 4
  | .tetrahedralDeficient p => Deficient.output p
  | .octahedralDeficient f p => if f=0 then Deficient.output p else Deficient.primeOutput p
  | .icosahedralDeficient o p => if o then Deficient.Opposite.output p else Deficient.output p
  | .mixedDeficient f p => Octahedral.deficientOutput f p
  | .tetrahedralReverse s => TetrahedralOrientation.card s
  | .octahedralFrame f frame order => Octahedral.output f frame order
  | .icosahedralFrame o i => if o then IcosahedralSeparator.Opposite.output i else IcosahedralSeparator.uniformOutput i

def SourceCase.group : SourceCase → Direction
  | .tetrahedralDeficient _ | .tetrahedralReverse _ => fun U => groupDirection .tetrahedral U
  | .octahedralDeficient f _ => OctahedralSeparator.Direction (Fin.castAdd 2 f)
  | .icosahedralDeficient o _ | .icosahedralFrame o _ =>
      if o then OppositeIcosahedral.Direction else fun U => groupDirection .icosahedral U
  | .mixedDeficient f _ => OctahedralSeparator.Direction (OctahedralSeparator.mixedForm f)
  | .octahedralFrame f _ _ => OctahedralSeparator.Direction f

/-- The finite list is explicit; no supplied coverage or exit oracle occurs. -/
theorem source_cases_count : Fintype.card SourceCase=201 := by decide +kernel

/-- Complete literal A.26: all listed marked-coordinate q have one of the three
terminal forms, witnessed by an actual native network obeying the resource bound. -/
theorem platonic_quaternary_exit_certificate (s : SourceCase) : Exit s.group s.signature := by
  cases s with
  | tetrahedralDeficient p => exact Deficient.tetrahedral p
  | octahedralDeficient f p =>
      fin_cases f
      · exact Deficient.octahedral p
      · exact Deficient.prime p
  | icosahedralDeficient o p =>
      cases o
      · exact Deficient.icosahedral p
      · exact Deficient.Opposite.exit p
  | mixedDeficient f p => exact Octahedral.all_mixed_deficient f p
  | tetrahedralReverse s => exact tetrahedral_reverse s
  | octahedralFrame f frame order => exact Octahedral.all_regular f frame order
  | icosahedralFrame o i =>
      cases o
      · exact Icosahedral.standard i
      · exact Icosahedral.opposite i

/-- The corresponding ordinary realization statement is derived from, rather
than substituted for, the literal network and resource-count certificate. -/
theorem platonic_quaternary_realized_exits (s : SourceCase) :
    (∃ t : Signature ℂ 4, Gadget.Realizes (resources s.group s.signature) .disequality t ∧
      TetrahedralOrientation.EndpointNondegenerateEightVertex t ∧
      ∀ r : Fin 3, (flatten r t).rank=2) ∨
    (∃ c : ℂ, c≠0 ∧ Gadget.Realizes (resources s.group s.signature) .disequality
      (c • OctahedralSeparator.complexEq4)) ∨
    ∃ B : Kernel ℂ, Gadget.Realizes (resources s.group s.signature) .disequality
      (OctahedralSeparator.Native.binarySignature B) ∧ Matrix.det (Matrix.of B)≠0 ∧
      ¬s.group (OctahedralSeparator.nativeTransfer B) := by
  rcases platonic_quaternary_exit_certificate s with ⟨t,h,he,hr⟩ | ⟨c,hc,h⟩ | ⟨B,h,hd,ho⟩
  · exact Or.inl ⟨t,h.realizes,he,hr⟩
  · exact Or.inr (Or.inl ⟨c,hc,h.realizes⟩)
  · exact Or.inr (Or.inr ⟨B,h.realizes,hd,ho⟩)

end
end Holant.Certificates.PlatonicQuaternaryExits
