import Holant.Pauli.ExoticKlein.SixPortProducts

/-! The forty-eight literal quaternary directions cover every actual oriented
matching of four original ports. The finite check proves only this small
endpoint-order normalization, not the six-port classification. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open scoped BigOperators

 def fourMatching (m : Fin 3) : Matching (Fin 4) 2 :=
  ⟨Equiv.ofBijective (fun p => fourPort m p.1 p.2) (by revert m; decide)⟩

 theorem directionTensor_matching (d : Direction) :
    directionTensor d = (fourMatching d.1).tensor ![d.2.1,d.2.2] := by
  rcases d with ⟨m,a,b⟩
  funext x
  fin_cases m <;>
    simp [directionTensor,directionTensorOver,fourMatching,fourPort,Matching.tensor,Fin.prod_univ_succ,E]

 def firstEdge (ports : Fin 2 × Bool → Fin 4) : Fin 2 :=
  if ports (0,false) = 0 ∨ ports (0,true) = 0 then 0 else 1

 def otherEdge (ports : Fin 2 × Bool → Fin 4) : Fin 2 := if firstEdge ports = 0 then 1 else 0

 def reverseFirst (ports : Fin 2 × Bool → Fin 4) : Bool := decide (ports (firstEdge ports,false) ≠ 0)
 def reverseOther (ports : Fin 2 × Bool → Fin 4) : Bool :=
  decide (ports (otherEdge ports,true) < ports (otherEdge ports,false))

 def canonicalShape (ports : Fin 2 × Bool → Fin 4) : Fin 3 :=
  Fin.ofNat 3 ((ports (firstEdge ports,!reverseFirst ports)).val-1)

 def canonicalDirection (ports : Fin 2 × Bool → Fin 4) (labels : Fin 2 → Label) : Direction :=
  (canonicalShape ports,
    (if reverseFirst ports then theta (labels (firstEdge ports)) else labels (firstEdge ports)),
    (if reverseOther ports then theta (labels (otherEdge ports)) else labels (otherEdge ports)))

 def canonicalScalar (ports : Fin 2 × Bool → Fin 4) (labels : Fin 2 → Label) : LinearCertificate.Q :=
  (if reverseFirst ports then gaussianTransposeScalar (labels (firstEdge ports)) else 1)*
  (if reverseOther ports then gaussianTransposeScalar (labels (otherEdge ports)) else 1)

 theorem canonicalScalar_nonzero (ports : Fin 2 × Bool → Fin 4) (labels : Fin 2 → Label) :
    canonicalScalar ports labels ≠ 0 := by
  unfold canonicalScalar
  apply mul_ne_zero
  · split <;> first | exact gaussianTransposeScalar_ne_zero _ | exact one_ne_zero
  · split <;> first | exact gaussianTransposeScalar_ne_zero _ | exact one_ne_zero

theorem canonical_ports (ports : Fin 2 × Bool → Fin 4) (hp : Function.Bijective ports) :
    (∀ b, ports (firstEdge ports,b) = fourPort (canonicalShape ports) 0
      (if reverseFirst ports then !b else b)) ∧
    (∀ b, ports (otherEdge ports,b) = fourPort (canonicalShape ports) 1
      (if reverseOther ports then !b else b)) := by
  revert ports hp
  decide +kernel

private theorem gaussian_orientation (reverse : Bool) (a : Label) (x y : Bool) :
    gaussianE a (if reverse then y else x) (if reverse then x else y) =
      (if reverse then gaussianTransposeScalar a else 1)*gaussianE (if reverse then theta a else a) x y := by
  cases reverse
  · simp
  · exact congrFun (congrFun (gaussian_transpose_E a) x) y

private theorem gaussianDirection_formula (d : Direction) (x : Fin 4 → Bool) :
    gaussianDirection d x =
      gaussianE d.2.1 (x (fourPort d.1 0 false)) (x (fourPort d.1 0 true))*
      gaussianE d.2.2 (x (fourPort d.1 1 false)) (x (fourPort d.1 1 true)) := by
  rcases d with ⟨m,a,b⟩
  fin_cases m <;> rfl

/-- Exact orientation normalization is reduced to a small finite endpoint
identity, followed by the already proved symbolic transpose calculus. -/
theorem canonical_gaussian_matching (ports : Fin 2 × Bool → Fin 4) (hp : Function.Bijective ports)
    (labels : Fin 2 → Label) (x : Fin 4 → Bool) :
    (∏ e : Fin 2, gaussianE (labels e) (x (ports (e,false))) (x (ports (e,true)))) =
      canonicalScalar ports labels*gaussianDirection (canonicalDirection ports labels) x := by
  have hprod (F : Fin 2 → LinearCertificate.Q) :
      ∏ e, F e = F (firstEdge ports)*F (otherEdge ports) := by
    have hh (e : Fin 2) : (∏ i, F i) = F e*F (if e = 0 then 1 else 0) := by
      fin_cases e <;> simp [Fin.prod_univ_succ,mul_comm]
    exact hh (firstEdge ports)
  rw [hprod]
  have ha := canonical_ports ports hp
  rw [ha.1 false,ha.1 true,ha.2 false,ha.2 true,gaussianDirection_formula]
  have hx (e : Fin 2) (r b : Bool) :
      x (fourPort (canonicalShape ports) e (if r then !b else b)) =
        if r then x (fourPort (canonicalShape ports) e (!b)) else x (fourPort (canonicalShape ports) e b) := by
    cases r <;> rfl
  rw [hx 0 (reverseFirst ports) false,hx 0 (reverseFirst ports) true,
    hx 1 (reverseOther ports) false,hx 1 (reverseOther ports) true]
  simp only [Bool.not_false,Bool.not_true]
  rw [gaussian_orientation,gaussian_orientation]
  unfold canonicalDirection canonicalScalar
  dsimp
  ring

 theorem matching_onDirection (M : Matching (Fin 4) 2) (labels : Fin 2 → Label) : OnDirection (M.tensor labels) := by
  refine ⟨canonicalDirection M.ports labels,Algebraic.gaussianToComplex (canonicalScalar M.ports labels),?_⟩
  funext x
  have h := congrArg Algebraic.gaussianToComplex (canonical_gaussian_matching M.ports M.ports.bijective labels x)
  simpa only [Matching.tensor,map_prod,map_mul,map_gaussianE,map_gaussianDirection] using h

 theorem onDirection_scale (h : Signature ℂ 4) (s : ℂ) (hh : OnDirection h) : OnDirection (fun x => s*h x) := by
  obtain ⟨d,t,rfl⟩ := hh
  exact ⟨d,s*t,by funext x; ring⟩

 theorem onDirection_iff_matching (h : Signature ℂ 4) : OnDirection h ↔
    h = 0 ∨ ∃ M : Matching (Fin 4) 2, ∃ labels : Fin 2 → Label, ∃ s : ℂ,
      s ≠ 0 ∧ h = fun x => s*M.tensor labels x := by
  constructor
  · rintro ⟨d,s,rfl⟩
    by_cases hs : s = 0
    · left; subst s; funext x; simp
    · right
      refine ⟨fourMatching d.1,![d.2.1,d.2.2],s,hs,?_⟩
      rw [directionTensor_matching]
  · rintro (rfl | ⟨M,labels,s,hs,rfl⟩)
    · exact zero_onDirection
    · exact onDirection_scale _ s (matching_onDirection M labels)

end
end Holant.Pauli.ExoticKlein.SixPort
