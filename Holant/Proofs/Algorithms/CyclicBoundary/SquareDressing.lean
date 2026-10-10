import Holant.Proofs.Algorithms.CyclicBoundary.BalancedBoundary


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.SquareDressing
open Holant.Projective.CyclicQuaternary Holant.Pauli.ExoticKlein.Fiber
open ZeroEndpointDressing PhysicalAttachments BalancedBoundary CoordinateFactors
noncomputable section

def sourceTable (p lam : ℂ) (a : Fin 3 → ℂ) : Signature ℂ 4 :=
  ofCoordinates p (p*lam) (fun i => (-p*lam/(a i),-p*a i))

def rootPhases (lam beta : ℂ) (a : Fin 3 → ℂ) : Fin 4 → ℂ :=
  ![beta/lam,a 0/beta,a 1/beta,a 2/beta]

theorem rootPhases_roots {N : ℕ} (lam beta : ℂ) (a : Fin 3 → ℂ)
    (hlam : lam^N=1) (hbeta : beta^N=1) (ha : ∀ i, (a i)^N=1) :
    ∀ j, (rootPhases lam beta a j)^N=1 := by
  intro j
  fin_cases j <;> simp [rootPhases,div_pow,hlam,hbeta,ha]

theorem rootPhases_nonzero (lam beta : ℂ) (a : Fin 3 → ℂ)
    (hlam : lam ≠ 0) (hbeta : beta ≠ 0) (ha : ∀ i, a i ≠ 0) :
    ∀ j, rootPhases lam beta a j ≠ 0 := by
  intro j
  fin_cases j <;> simp [rootPhases,hlam,hbeta,ha]

/-- The square condition enters only through the explicit beta, with no
unrestricted complex square root substituted for a finite-order root. -/
theorem dress_source (p lam beta : ℂ) (a : Fin 3 → ℂ)
    (hlam : lam ≠ 0) (hbeta : beta ≠ 0) (ha : ∀ i, a i ≠ 0)
    (hsquare : beta^2=a 0*a 1*a 2) :
    dress (sourceTable p lam a) (rootPhases lam beta a) = balanced p (fun _ => -p) := by
  have ha2 : a 2 = beta^2/(a 0*a 1) := by
    apply (eq_div_iff (mul_ne_zero (ha 0) (ha 1))).mpr
    linear_combination -hsquare
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [dress,sourceTable,rootPhases,balanced,ofCoordinates,Fin.prod_univ_succ,
      h0,h1,h2,h3,ha2]
  all_goals field_simp [ha 0,ha 1,hbeta,hlam]
  all_goals ring

theorem dressed_endpoints (p lam beta : ℂ) (a : Fin 3 → ℂ)
    (hlam : lam ≠ 0) (hbeta : beta ≠ 0) (ha : ∀ i, a i ≠ 0)
    (hsquare : beta^2=a 0*a 1*a 2) :
    physical (dress (sourceTable p lam a) (rootPhases lam beta a)) (fun _ => false) = -4*p ∧
    physical (dress (sourceTable p lam a) (rootPhases lam beta a)) (fun _ => true) = -4*p := by
  rw [dress_source p lam beta a hlam hbeta ha hsquare,physical_balanced]
  constructor <;> simp [balanced,ofCoordinates] <;> ring

theorem square_branch {F : SignatureFamily ℂ} {N : ℕ} (R : Representatives F N)
    (hN : 0 < N) (p lam beta : ℂ) (a : Fin 3 → ℂ)
    (hp : p ≠ 0) (hlam : lam^N=1) (hbeta : beta^N=1) (ha : ∀ i, (a i)^N=1)
    (hsquare : beta^2=a 0*a 1*a 2)
    (hq : Gadget.RealizesUpTo F .disequality (physical (sourceTable p lam a)))
    (hprime : ¬HasProperTensorFactor (physical (sourceTable p lam a))) :
    Gadget.RealizesUpTo F .disequality (physical (balanced p (fun _ => -p))) ∧
      EvenSupported (physical (balanced p (fun _ => -p))) ∧
      physical (balanced p (fun _ => -p)) (fun _ => false) ≠ 0 ∧
      physical (balanced p (fun _ => -p)) (fun _ => true) ≠ 0 ∧
      ¬HasProperTensorFactor (physical (balanced p (fun _ => -p))) := by
  have hl0 := Holant.Projective.CyclicPhasePencil.root_ne_zero hN hlam
  have hb0 := Holant.Projective.CyclicPhasePencil.root_ne_zero hN hbeta
  have ha0 : ∀ i, a i ≠ 0 := fun i => Holant.Projective.CyclicPhasePencil.root_ne_zero hN (ha i)
  have hreal := phase_dressing_upTo R _ hq _ (rootPhases_roots lam beta a hlam hbeta ha)
  have he := dress_source p lam beta a hl0 hb0 ha0 hsquare
  rw [he] at hreal
  have hends := dressed_endpoints p lam beta a hl0 hb0 ha0 hsquare
  rw [he] at hends
  refine ⟨hreal,?_,?_,?_,?_⟩
  · rw [physical_balanced]
    exact balanced_even _ _
  · rw [hends.1]
    exact mul_ne_zero (by norm_num) hp
  · rw [hends.2]
    exact mul_ne_zero (by norm_num) hp
  · intro h
    apply hprime
    apply (physical_factor_iff _).2
    apply (dress_factor_iff _ _ (rootPhases_nonzero lam beta a hl0 hb0 ha0)).mp
    rw [he]
    exact (physical_factor_iff _).mp h

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.SquareDressing
