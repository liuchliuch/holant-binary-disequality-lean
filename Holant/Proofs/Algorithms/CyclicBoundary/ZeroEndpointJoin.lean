import Holant.Proofs.Algorithms.CyclicBoundary.ZeroEndpointFactor
import Holant.Proofs.Algorithms.CyclicBoundary.TwoCopyKernels


namespace Holant.LocalDrafts.MainChain.CyclicBoundary.ZeroEndpointJoin
open Holant.Projective.CyclicQuaternary
open Holant.Certificates.FourthRootOdd
open Holant.Certificates.TwelveLoops
open ZeroEndpointFactor TwoCopyKernels
noncomputable section

def other₁ : Fin 3 → Fin 3 := ![1,0,0]
def other₂ : Fin 3 → Fin 3 := ![2,2,1]
def selected (i : Fin 3) : Fin 6 := ⟨i.val, by omega⟩

def join (r a : Fin 3 → ℂ) (i : Fin 3) : Network ℂ 4 :=
  network (table r a) (table r a) (selected i)
    (diagonal 1 (-(a (other₁ i) * a (other₂ i)))) Signature.equality

def endpoint₀ (r a : Fin 3 → ℂ) (i : Fin 3) : ℂ :=
  -(a (other₁ i) * a (other₂ i)) * (r i)^2
def endpoint₁ (r a : Fin 3 → ℂ) (i : Fin 3) : ℂ := (a i)^2 * (r i)^2
def middle₀ (r a : Fin 3 → ℂ) (i : Fin 3) : ℂ :=
  a (other₁ i) * (ZeroEndpointFactor.weight r a (other₁ i) - ZeroEndpointFactor.weight r a (other₂ i))
def middle₁ (r a : Fin 3 → ℂ) (i : Fin 3) : ℂ :=
  -a (other₂ i) * (ZeroEndpointFactor.weight r a (other₁ i) - ZeroEndpointFactor.weight r a (other₂ i))

/-- Exact output order is the two surviving ports of copy one followed by
the two surviving ports of copy two. middle₀ is at 0101, middle₁ at 1010. -/
theorem join_denote (r a : Fin 3 → ℂ) (i : Fin 3) :
    (join r a i).denote = ofCoordinates (endpoint₀ r a i) (endpoint₁ r a i)
      ![(0,0),(middle₁ r a i,middle₀ r a i),(0,0)] := by
  rw [join, network_denote]
  funext x
  rw [diagonal_equality]
  fin_cases i <;>
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [table, ofCoordinates, selected, other₁, other₂, insertPair,
      portEquiv, portInverse, firstHalf, secondHalf, endpoint₀, endpoint₁,
      middle₀, middle₁, ZeroEndpointFactor.weight, h0,h1,h2,h3] <;> ring

def delta (r a : Fin 3 → ℂ) (i : Fin 3) : ℂ :=
  ZeroEndpointMinors.minor (ZeroEndpointFactor.weight r a i)
    (ZeroEndpointFactor.weight r a (other₁ i)) (ZeroEndpointFactor.weight r a (other₂ i))

/-- The logical matching-code flattening has this actual 2-by-2 determinant. -/
theorem logical_determinant (r a : Fin 3 → ℂ) (i : Fin 3) :
    endpoint₀ r a i * endpoint₁ r a i - middle₀ r a i * middle₁ r a i =
      a (other₁ i) * a (other₂ i) * delta r a i := by
  simp only [endpoint₀, endpoint₁, middle₀, middle₁, delta,
    ZeroEndpointMinors.minor, ZeroEndpointFactor.weight]
  ring

theorem logical_determinant_ne_zero (r a : Fin 3 → ℂ) (ha : ∀ k, a k ≠ 0)
    (i : Fin 3) (hd : delta r a i ≠ 0) :
    endpoint₀ r a i * endpoint₁ r a i - middle₀ r a i * middle₁ r a i ≠ 0 := by
  rw [logical_determinant]
  exact mul_ne_zero (mul_ne_zero (ha _) (ha _)) hd

end
end Holant.LocalDrafts.MainChain.CyclicBoundary.ZeroEndpointJoin
