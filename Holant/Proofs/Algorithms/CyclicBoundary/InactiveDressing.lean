import Holant.Proofs.Algorithms.CyclicBoundary.SquareDressing
import Holant.Proofs.Algorithms.CyclicBoundary.ZeroEndpointJoin


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.InactiveDressing
open Holant.Projective.CyclicQuaternary Holant.Pauli.ExoticKlein.Fiber
open ZeroEndpointDressing PhysicalAttachments BalancedBoundary CoordinateFactors SquareDressing
open ZeroEndpointJoin
noncomputable section

def maskedTable (p lam : ℂ) (active : Fin 3 → Bool) (a : Fin 3 → ℂ) : Signature ℂ 4 :=
  ofCoordinates p (p*lam) (fun i => if active i then (-p*lam/a i,-p*a i) else (0,0))

def filledRoots (a : Fin 3 → ℂ) (i : Fin 3) : Fin 3 → ℂ :=
  fun k => if k=i then (a (other₁ i)*a (other₂ i))⁻¹ else a k

theorem filled_roots {N : ℕ} (a : Fin 3 → ℂ) (ha : ∀ k, (a k)^N=1)
    (i : Fin 3) : ∀ k, (filledRoots a i k)^N=1 := by
  intro k
  by_cases hk : k=i
  · simp [filledRoots,hk,inv_pow,mul_pow,ha]
  · simp [filledRoots,hk,ha]

theorem filled_product (a : Fin 3 → ℂ) (ha : ∀ k, a k ≠ 0) (i : Fin 3) :
    filledRoots a i 0 * filledRoots a i 1 * filledRoots a i 2 = 1 := by
  fin_cases i <;> simp [filledRoots,other₁,other₂]
  all_goals field_simp [ha 0,ha 1,ha 2]
  all_goals ring

theorem inactive_unchanged (p lam : ℂ) (active : Fin 3 → Bool) (a : Fin 3 → ℂ)
    (i : Fin 3) (hi : active i=false) :
    maskedTable p lam active (filledRoots a i) = maskedTable p lam active a := by
  unfold maskedTable
  congr 1
  funext k
  by_cases hk : k=i
  · subst k
    simp [hi]
  · simp [filledRoots,hk]

theorem masked_dress (p lam beta : ℂ) (active : Fin 3 → Bool) (a : Fin 3 → ℂ)
    (hlam : lam ≠ 0) (hbeta : beta ≠ 0) (ha : ∀ i, a i ≠ 0)
    (hsquare : beta^2=a 0*a 1*a 2) :
    dress (maskedTable p lam active a) (rootPhases lam beta a) =
      balanced p (fun i => if active i then -p else 0) := by
  have ha2 : a 2 = beta^2/(a 0*a 1) := by
    apply (eq_div_iff (mul_ne_zero (ha 0) (ha 1))).mpr
    linear_combination -hsquare
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [dress,maskedTable,rootPhases,balanced,ofCoordinates,Fin.prod_univ_succ,
      h0,h1,h2,h3,ha2]
  all_goals try split_ifs
  all_goals field_simp [ha 0,ha 1,hbeta,hlam]
  all_goals ring

theorem physical_dress_nonzero (q : Signature ℂ 4) (s : Fin 4 → ℂ)
    (hs : ∀ i, s i ≠ 0) (hq : physical q ≠ 0) : physical (dress q s) ≠ 0 := by
  have hn : q ≠ 0 := fun h => hq ((physical_zero_iff _).2 h)
  have hd := action_nonzero (fun i => phase (s i)) (fun i => phase ((s i)⁻¹))
    (fun i => (phase_inverse _ (hs i)).1) q hn
  rw [←dress_eq_action] at hd
  exact fun h => hd ((physical_zero_iff _).1 h)

theorem physical_dress_prime (q : Signature ℂ 4) (s : Fin 4 → ℂ)
    (hs : ∀ i, s i ≠ 0) (hp : ¬HasProperTensorFactor (physical q)) :
    ¬HasProperTensorFactor (physical (dress q s)) := by
  intro h
  apply hp
  exact (physical_factor_iff _).2
    ((dress_factor_iff q s hs).1 ((physical_factor_iff _).1 h))

theorem inactive_boundary {F : SignatureFamily ℂ} {N : ℕ} (R : Representatives F N)
    (hNpos : 0 < N) (hNeven : Even N) (p lam : ℂ)
    (active : Fin 3 → Bool) (a : Fin 3 → ℂ) (i : Fin 3) (hi : active i=false)
    (hlam : lam^N=1) (ha : ∀ k, (a k)^N=1)
    (hq : Gadget.RealizesUpTo F .disequality (physical (maskedTable p lam active a)))
    (hn : physical (maskedTable p lam active a) ≠ 0)
    (hp : ¬HasProperTensorFactor (physical (maskedTable p lam active a))) :
    ∃ g : Signature ℂ 4, Gadget.RealizesUpTo F .disequality g ∧
      EvenSupported g ∧ g (fun _ => false) ≠ 0 ∧ g (fun _ => true) ≠ 0 ∧
      ¬HasProperTensorFactor g := by
  let b := filledRoots a i
  have ha0 : ∀ k, a k ≠ 0 := fun k => Holant.Projective.CyclicPhasePencil.root_ne_zero hNpos (ha k)
  have hb : ∀ k, (b k)^N=1 := filled_roots a ha i
  have hb0 : ∀ k, b k ≠ 0 := fun k => Holant.Projective.CyclicPhasePencil.root_ne_zero hNpos (hb k)
  have hl0 := Holant.Projective.CyclicPhasePencil.root_ne_zero hNpos hlam
  have hsquare : (1:ℂ)^2=b 0*b 1*b 2 := by
    simpa only [one_pow] using (filled_product a ha0 i).symm
  have heq : maskedTable p lam active b = maskedTable p lam active a := inactive_unchanged p lam active a i hi
  have hq' : Gadget.RealizesUpTo F .disequality (physical (maskedTable p lam active b)) := by rwa [heq]
  have hn' : physical (maskedTable p lam active b) ≠ 0 := by rwa [heq]
  have hp' : ¬HasProperTensorFactor (physical (maskedTable p lam active b)) := by rwa [heq]
  have hs := rootPhases_roots lam 1 b hlam (one_pow N) hb
  have hs0 := rootPhases_nonzero lam 1 b hl0 one_ne_zero hb0
  have hreal := phase_dressing_upTo R _ hq' _ hs
  have hnonzero := physical_dress_nonzero _ _ hs0 hn'
  have hprime := physical_dress_prime _ _ hs0 hp'
  have hbalanced := masked_dress p lam 1 active b hl0 one_ne_zero hb0 hsquare
  rw [hbalanced] at hreal hnonzero hprime
  obtain ⟨x,hx,he,h0,h1,hp⟩ := balanced_to_endpoint R hNeven p _ hreal hnonzero hprime
  exact ⟨_,hx,he,h0,h1,hp⟩

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.InactiveDressing
