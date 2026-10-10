import Holant.Certificates.EqualityQuaternary.KleinClassification
import Holant.Certificates.EqualityQuaternary.KleinOrbitCoverage
import Holant.Certificates.EqualityQuaternary.StandardKleinSource
import Holant.Certificates.EqualityQuaternary.BoundaryResources

/-! Complete exotic Klein row of A.7/A.8. Safe-locus classification, orbit
reduction, actual fixed representative scalars, and the endpoint-zero
exception are all derived before constructing the final one-q gadget.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.Klein
open Holant Holant.Marked Holant.Tractable
open Holant.EightVertex.ProductAnchor (EndpointEven)
open Finite Orbit
set_option backward.isDefEq.respectTransparency false

theorem source_exotic_representative {F : SignatureFamily Scalar}
    (reps : Representatives F .exotic) (q : Signature Scalar 4) (h : PhysicalDeck reps q) :
    ∃ j : Fin 24,Representative (actualRun reps (paths j) q) := by
  obtain ⟨p,c,j,hq,hplane⟩ := source_klein_plane reps q h
  have he : q=fun w => ∑ r : Fin 4,coefficientVector p c (pivots .exotic j r)*planeTensor .exotic j r w := by
    funext w
    rw [hq]
    exact plane_expansion .exotic p c j hplane w
  have hideal : Representative (run (E .exotic) (paths j) q) := by
    rw [he,run_combination]
    exact representative_combination _ _ (fun r => orbit_checked j (all_orbit_checks j) r)
  refine ⟨j,?_⟩
  rw [actualRun_scale]
  exact representative_smul _ hideal

def exoticFinalNetwork {F : SignatureFamily Scalar}
    (reps : Representatives F .exotic) (q : Signature Scalar 4) (j : Fin 24) (flip : Bool) :
    Network Scalar 4 :=
  let N := netRun reps (paths j) (Counted.input q)
  if flip then Boundary.flipLastTwo N else N

/-- The 24-plane atlas is reduced by explicit group words, and every word
is implemented with the caller's actual binary representatives on one q.
The actual normalizing word and the exceptional two-leg flip are exposed. -/
theorem source_exotic_choice (F : SignatureFamily Scalar)
    (reps : Representatives F .exotic) (hret : Retained reps) (q : Signature Scalar 4) (hp : TensorPrime q)
    (hq : (⟨4,q⟩ : AnySignature Scalar)∈F)
    (hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature Scalar)∈F)
    (hd : PhysicalDeck reps q) :
    ∃ (j : Fin 24) (flip : Bool), let N := exoticFinalNetwork reps q j flip
      Boundary.CoreLabels q N ∧ Boundary.Native N ∧ Counted.copies N=1 ∧
      EndpointEven N.denote ∧ TensorPrime N.denote ∧ ¬GroupMatching (group .exotic) N.denote ∧
      Gadget.Realizes F .disequality N.denote ∧ Boundary.Uses F N := by
  obtain ⟨j,hrep⟩ := source_exotic_representative reps q hd
  let N := netRun reps (paths j) (Counted.input q)
  have hN : N.denote=actualRun reps (paths j) q := by
    dsimp only [N]
    rw [netRun_denote,Counted.input_denote]
  have hprime : TensorPrime N.denote := by
    rw [hN]
    exact actualRun_prime reps (paths j) hp
  have hactual : Gadget.Realizes F .disequality N.denote := by
    rw [hN]
    exact actualRun_realizes reps (paths j) (Gadget.realizes_of_mem F .disequality q hq)
  have hlabels : Boundary.CoreLabels q N :=
    netRun_labels reps (paths j) (fun _ => Or.inl rfl)
  have hnative : Boundary.Native N := netRun_native reps (paths j) (fun e => Fin.elim0 e)
  have hcopies : Counted.copies N=1 := by
    dsimp only [N]
    rw [netRun_copies,Counted.input_copies]
  have huses : Boundary.Uses F N := netRun_uses reps hret (paths j) (fun _ => hq)
  have hrepN : Representative N.denote := by rw [hN]; exact hrep
  have hplane := representative_plane hrepN
  let a := (N.denote (fun _ => false)+N.denote ![false,false,true,true])/2
  let b := (N.denote ![false,false,true,true]-N.denote (fun _ => false))/4
  have hplane' : N.denote=Exotic.plane a b := hplane
  obtain ⟨mask,hmask,he⟩ := Exotic.representative_endpoint a b (hplane' ▸ hprime.1)
  have he' : EndpointEven (Flip.value N.denote mask) := by rwa [hplane']
  rcases hmask with hmask | hmask
  · have hflip : Flip.value N.denote mask=N.denote := by
      rw [hmask]
      funext w
      apply congrArg N.denote
      funext i
      simp [Holant.Marked.SupportAtlas.xorWord]
    refine ⟨j,false,hlabels,hnative,hcopies,?_,hprime,prime_not_matching hprime,hactual,huses⟩
    rwa [hflip] at he'
  · have hvalue : (Boundary.flipLastTwo N).denote=Flip.value N.denote mask := by
      rw [Boundary.flipLastTwo_denote,hmask]
      rfl
    have hp' : TensorPrime (Boundary.flipLastTwo N).denote := by
      rw [hvalue]
      exact flip_prime hprime mask
    refine ⟨j,true,?_,?_,?_,?_,hp',prime_not_matching hp',?_,Boundary.flipLastTwo_uses huses hI⟩
    · exact Boundary.attach_labels (Boundary.attach_labels hlabels 2 Signature.equality) 3 Signature.equality
    · exact Boundary.attach_native (Boundary.attach_native hnative 2 Signature.equality) 3 Signature.equality
    · change Counted.copies (Boundary.flipLastTwo N)=1
      rw [Boundary.flipLastTwo_copies,hcopies]
    · change EndpointEven (Boundary.flipLastTwo N).denote
      rwa [hvalue]
    · change Gadget.Realizes F .disequality (Boundary.flipLastTwo N).denote
      rw [hvalue]
      exact Flip.actual F N.denote hactual (Gadget.realizes_of_mem F .disequality _ hI) mask

/-- Complete exotic Klein boundary, projected from the explicit choice. -/
theorem source_exotic_boundary (F : SignatureFamily Scalar)
    (reps : Representatives F .exotic) (hret : Retained reps) (q : Signature Scalar 4) (hp : TensorPrime q)
    (hq : (⟨4,q⟩ : AnySignature Scalar)∈F)
    (hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature Scalar)∈F)
    (hd : PhysicalDeck reps q) :
    ∃ N : Network Scalar 4,Boundary.CoreLabels q N ∧ Boundary.Native N ∧ Counted.copies N=1 ∧
      EndpointEven N.denote ∧ TensorPrime N.denote ∧ ¬GroupMatching (group .exotic) N.denote ∧
      Gadget.Realizes F .disequality N.denote ∧ Boundary.Uses F N := by
  obtain ⟨j,flip,h⟩ := source_exotic_choice F reps hret q hp hq hI hd
  exact ⟨exoticFinalNetwork reps q j flip,h⟩

end Holant.Certificates.EqualityQuaternary.Klein
