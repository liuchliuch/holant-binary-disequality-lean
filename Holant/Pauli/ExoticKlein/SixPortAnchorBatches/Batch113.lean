import Holant.Pauli.ExoticKlein.SixPortCachedIntegerProblem
import Holant.Pauli.ExoticKlein.SixPortAnchorWitness

namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open IntegerCertificate
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def arep3198State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 1),some (directionEquiv 15)]

def arep3198Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,1),(6,(⟨(-2),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 10, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-2),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-2),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3198Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3198Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3198Node0Reductions arep3198Node0Children

theorem arep3198_cached_checked :
    arep3198Node0.check (cachedIntegerProblem arep3198State) (integerInitialRows arep3198State) = true := by
  decide +kernel

theorem arep3198_checked :
    arep3198Node0.check (integerProblem arep3198State) (integerInitialRows arep3198State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3198_cached_checked

theorem arep3198_solved : Solved arep3198State :=
  solved_of_integer_certificate arep3198State arep3198Node0 arep3198_checked

theorem arep3198_representative : Solved (stateEquiv (representativeCode 3198)) := by
  have he : stateEquiv (representativeCode 3198) = arep3198State := by decide +kernel
  rw [he]
  exact arep3198_solved

theorem anchorEntry1808_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 1808))) := by
  have he : anchorRepresentative 1808 = 3198 := by decide +kernel
  rw [he]
  exact arep3198_representative

def arep3199State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 1),some (directionEquiv 16)]

def arep3199Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(16,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(2)⟩ : GZ)),(8,(⟨(0),(-2)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,1),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(7,(⟨(0),(2)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(4)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(4)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,1),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1),(6,(⟨(2),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3199Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3199Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3199Node0Reductions arep3199Node0Children

theorem arep3199_cached_checked :
    arep3199Node0.check (cachedIntegerProblem arep3199State) (integerInitialRows arep3199State) = true := by
  decide +kernel

theorem arep3199_checked :
    arep3199Node0.check (integerProblem arep3199State) (integerInitialRows arep3199State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3199_cached_checked

theorem arep3199_solved : Solved arep3199State :=
  solved_of_integer_certificate arep3199State arep3199Node0 arep3199_checked

theorem arep3199_representative : Solved (stateEquiv (representativeCode 3199)) := by
  have he : stateEquiv (representativeCode 3199) = arep3199State := by decide +kernel
  rw [he]
  exact arep3199_solved

theorem anchorEntry1809_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 1809))) := by
  have he : anchorRepresentative 1809 = 3199 := by decide +kernel
  rw [he]
  exact arep3199_representative

def arep3200State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 1),some (directionEquiv 17)]

def arep3200Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3200Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3200Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3200Node0Reductions arep3200Node0Children

theorem arep3200_cached_checked :
    arep3200Node0.check (cachedIntegerProblem arep3200State) (integerInitialRows arep3200State) = true := by
  decide +kernel

theorem arep3200_checked :
    arep3200Node0.check (integerProblem arep3200State) (integerInitialRows arep3200State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3200_cached_checked

theorem arep3200_solved : Solved arep3200State :=
  solved_of_integer_certificate arep3200State arep3200Node0 arep3200_checked

theorem arep3200_representative : Solved (stateEquiv (representativeCode 3200)) := by
  have he : stateEquiv (representativeCode 3200) = arep3200State := by decide +kernel
  rw [he]
  exact arep3200_solved

theorem anchorEntry1810_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 1810))) := by
  have he : anchorRepresentative 1810 = 3200 := by decide +kernel
  rw [he]
  exact arep3200_representative

def arep3201State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 1),some (directionEquiv 18)]

def arep3201Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,1),(6,(⟨(2),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(11,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3201Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3201Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3201Node0Reductions arep3201Node0Children

theorem arep3201_cached_checked :
    arep3201Node0.check (cachedIntegerProblem arep3201State) (integerInitialRows arep3201State) = true := by
  decide +kernel

theorem arep3201_checked :
    arep3201Node0.check (integerProblem arep3201State) (integerInitialRows arep3201State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3201_cached_checked

theorem arep3201_solved : Solved arep3201State :=
  solved_of_integer_certificate arep3201State arep3201Node0 arep3201_checked

theorem arep3201_representative : Solved (stateEquiv (representativeCode 3201)) := by
  have he : stateEquiv (representativeCode 3201) = arep3201State := by decide +kernel
  rw [he]
  exact arep3201_solved

theorem anchorEntry1811_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 1811))) := by
  have he : anchorRepresentative 1811 = 3201 := by decide +kernel
  rw [he]
  exact arep3201_representative

def arep3202State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 1),some (directionEquiv 19)]

def arep3202Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(3),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(-4)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(3),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(3),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(8,(⟨(0),(-1)⟩ : GZ)),(10,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3202Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3202Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3202Node0Reductions arep3202Node0Children

theorem arep3202_cached_checked :
    arep3202Node0.check (cachedIntegerProblem arep3202State) (integerInitialRows arep3202State) = true := by
  decide +kernel

theorem arep3202_checked :
    arep3202Node0.check (integerProblem arep3202State) (integerInitialRows arep3202State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3202_cached_checked

theorem arep3202_solved : Solved arep3202State :=
  solved_of_integer_certificate arep3202State arep3202Node0 arep3202_checked

theorem arep3202_representative : Solved (stateEquiv (representativeCode 3202)) := by
  have he : stateEquiv (representativeCode 3202) = arep3202State := by decide +kernel
  rw [he]
  exact arep3202_solved

theorem anchorEntry1812_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 1812))) := by
  have he : anchorRepresentative 1812 = 3202 := by decide +kernel
  rw [he]
  exact arep3202_representative

def arep3203State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 1),some (directionEquiv 20)]

def arep3203Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(7,(⟨(0),(2)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 10, weights := [(5,(⟨(0),(-3)⟩ : GZ)),(7,(⟨(4),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(3),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,1),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-2)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-3)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(-2)⟩ : GZ)),(7,(⟨(3),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,1),(7,(⟨(0),(1)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-2)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-3)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3203Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3203Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3203Node0Reductions arep3203Node0Children

theorem arep3203_cached_checked :
    arep3203Node0.check (cachedIntegerProblem arep3203State) (integerInitialRows arep3203State) = true := by
  decide +kernel

theorem arep3203_checked :
    arep3203Node0.check (integerProblem arep3203State) (integerInitialRows arep3203State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3203_cached_checked

theorem arep3203_solved : Solved arep3203State :=
  solved_of_integer_certificate arep3203State arep3203Node0 arep3203_checked

theorem arep3203_representative : Solved (stateEquiv (representativeCode 3203)) := by
  have he : stateEquiv (representativeCode 3203) = arep3203State := by decide +kernel
  rw [he]
  exact arep3203_solved

theorem anchorEntry1813_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 1813))) := by
  have he : anchorRepresentative 1813 = 3203 := by decide +kernel
  rw [he]
  exact arep3203_representative

def arep3204State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 1),some (directionEquiv 21)]

def arep3204Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3204Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3204Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3204Node0Reductions arep3204Node0Children

theorem arep3204_cached_checked :
    arep3204Node0.check (cachedIntegerProblem arep3204State) (integerInitialRows arep3204State) = true := by
  decide +kernel

theorem arep3204_checked :
    arep3204Node0.check (integerProblem arep3204State) (integerInitialRows arep3204State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3204_cached_checked

theorem arep3204_solved : Solved arep3204State :=
  solved_of_integer_certificate arep3204State arep3204Node0 arep3204_checked

theorem arep3204_representative : Solved (stateEquiv (representativeCode 3204)) := by
  have he : stateEquiv (representativeCode 3204) = arep3204State := by decide +kernel
  rw [he]
  exact arep3204_solved

theorem anchorEntry1814_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 1814))) := by
  have he : anchorRepresentative 1814 = 3204 := by decide +kernel
  rw [he]
  exact arep3204_representative

def arep3205State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 1),some (directionEquiv 22)]

def arep3205Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-4),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(4),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(-4)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(4),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(9,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3205Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3205Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3205Node0Reductions arep3205Node0Children

theorem arep3205_cached_checked :
    arep3205Node0.check (cachedIntegerProblem arep3205State) (integerInitialRows arep3205State) = true := by
  decide +kernel

theorem arep3205_checked :
    arep3205Node0.check (integerProblem arep3205State) (integerInitialRows arep3205State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3205_cached_checked

theorem arep3205_solved : Solved arep3205State :=
  solved_of_integer_certificate arep3205State arep3205Node0 arep3205_checked

theorem arep3205_representative : Solved (stateEquiv (representativeCode 3205)) := by
  have he : stateEquiv (representativeCode 3205) = arep3205State := by decide +kernel
  rw [he]
  exact arep3205_solved

theorem anchorEntry1815_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 1815))) := by
  have he : anchorRepresentative 1815 = 3205 := by decide +kernel
  rw [he]
  exact arep3205_representative

def arep3206State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 1),some (directionEquiv 23)]

def arep3206Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(4),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-4),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-4),(0)⟩ : GZ)),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 8, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3206Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3206Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3206Node0Reductions arep3206Node0Children

theorem arep3206_cached_checked :
    arep3206Node0.check (cachedIntegerProblem arep3206State) (integerInitialRows arep3206State) = true := by
  decide +kernel

theorem arep3206_checked :
    arep3206Node0.check (integerProblem arep3206State) (integerInitialRows arep3206State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3206_cached_checked

theorem arep3206_solved : Solved arep3206State :=
  solved_of_integer_certificate arep3206State arep3206Node0 arep3206_checked

theorem arep3206_representative : Solved (stateEquiv (representativeCode 3206)) := by
  have he : stateEquiv (representativeCode 3206) = arep3206State := by decide +kernel
  rw [he]
  exact arep3206_solved

theorem anchorEntry1816_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 1816))) := by
  have he : anchorRepresentative 1816 = 3206 := by decide +kernel
  rw [he]
  exact arep3206_representative

def arep3207State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 1),some (directionEquiv 24)]

def arep3207Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-3),(0)⟩ : GZ)),(7,(⟨(0),(-2)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(2),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 10, weights := [(5,(⟨(3),(0)⟩ : GZ)),(7,(⟨(0),(4)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(2),(0)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(2)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(0),(1)⟩ : GZ)),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,1),(7,(⟨(0),(2)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-2)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3207Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3207Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3207Node0Reductions arep3207Node0Children

theorem arep3207_cached_checked :
    arep3207Node0.check (cachedIntegerProblem arep3207State) (integerInitialRows arep3207State) = true := by
  decide +kernel

theorem arep3207_checked :
    arep3207Node0.check (integerProblem arep3207State) (integerInitialRows arep3207State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3207_cached_checked

theorem arep3207_solved : Solved arep3207State :=
  solved_of_integer_certificate arep3207State arep3207Node0 arep3207_checked

theorem arep3207_representative : Solved (stateEquiv (representativeCode 3207)) := by
  have he : stateEquiv (representativeCode 3207) = arep3207State := by decide +kernel
  rw [he]
  exact arep3207_solved

theorem anchorEntry1817_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 1817))) := by
  have he : anchorRepresentative 1817 = 3207 := by decide +kernel
  rw [he]
  exact arep3207_representative

def arep3208State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 1),some (directionEquiv 25)]

def arep3208Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3208Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3208Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3208Node0Reductions arep3208Node0Children

theorem arep3208_cached_checked :
    arep3208Node0.check (cachedIntegerProblem arep3208State) (integerInitialRows arep3208State) = true := by
  decide +kernel

theorem arep3208_checked :
    arep3208Node0.check (integerProblem arep3208State) (integerInitialRows arep3208State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3208_cached_checked

theorem arep3208_solved : Solved arep3208State :=
  solved_of_integer_certificate arep3208State arep3208Node0 arep3208_checked

theorem arep3208_representative : Solved (stateEquiv (representativeCode 3208)) := by
  have he : stateEquiv (representativeCode 3208) = arep3208State := by decide +kernel
  rw [he]
  exact arep3208_solved

theorem anchorEntry1818_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 1818))) := by
  have he : anchorRepresentative 1818 = 3208 := by decide +kernel
  rw [he]
  exact arep3208_representative

def arep3209State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 1),some (directionEquiv 26)]

def arep3209Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(2),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,1),(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(-3)⟩ : GZ)),(5,1),(6,(⟨(2),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(8,(⟨(0),(1)⟩ : GZ)),(12,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,1),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3209Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3209Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3209Node0Reductions arep3209Node0Children

theorem arep3209_cached_checked :
    arep3209Node0.check (cachedIntegerProblem arep3209State) (integerInitialRows arep3209State) = true := by
  decide +kernel

theorem arep3209_checked :
    arep3209Node0.check (integerProblem arep3209State) (integerInitialRows arep3209State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3209_cached_checked

theorem arep3209_solved : Solved arep3209State :=
  solved_of_integer_certificate arep3209State arep3209Node0 arep3209_checked

theorem arep3209_representative : Solved (stateEquiv (representativeCode 3209)) := by
  have he : stateEquiv (representativeCode 3209) = arep3209State := by decide +kernel
  rw [he]
  exact arep3209_solved

theorem anchorEntry1819_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 1819))) := by
  have he : anchorRepresentative 1819 = 3209 := by decide +kernel
  rw [he]
  exact arep3209_representative

def arep3210State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 1),some (directionEquiv 27)]

def arep3210Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-2),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(2),(0)⟩ : GZ)),(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(4,(⟨(0),(3)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(1)⟩ : GZ)),(6,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(2)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,1),(8,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1),(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(4,(⟨(0),(-1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(6,(⟨(-1),(0)⟩ : GZ)),(7,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(6,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ)),(5,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3210Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3210Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3210Node0Reductions arep3210Node0Children

theorem arep3210_cached_checked :
    arep3210Node0.check (cachedIntegerProblem arep3210State) (integerInitialRows arep3210State) = true := by
  decide +kernel

theorem arep3210_checked :
    arep3210Node0.check (integerProblem arep3210State) (integerInitialRows arep3210State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3210_cached_checked

theorem arep3210_solved : Solved arep3210State :=
  solved_of_integer_certificate arep3210State arep3210Node0 arep3210_checked

theorem arep3210_representative : Solved (stateEquiv (representativeCode 3210)) := by
  have he : stateEquiv (representativeCode 3210) = arep3210State := by decide +kernel
  rw [he]
  exact arep3210_solved

theorem anchorEntry1820_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 1820))) := by
  have he : anchorRepresentative 1820 = 3210 := by decide +kernel
  rw [he]
  exact arep3210_representative

def arep3211State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 1),some (directionEquiv 28)]

def arep3211Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(7,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1),(8,(⟨(0),(1)⟩ : GZ)),(10,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3211Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3211Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3211Node0Reductions arep3211Node0Children

theorem arep3211_cached_checked :
    arep3211Node0.check (cachedIntegerProblem arep3211State) (integerInitialRows arep3211State) = true := by
  decide +kernel

theorem arep3211_checked :
    arep3211Node0.check (integerProblem arep3211State) (integerInitialRows arep3211State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3211_cached_checked

theorem arep3211_solved : Solved arep3211State :=
  solved_of_integer_certificate arep3211State arep3211Node0 arep3211_checked

theorem arep3211_representative : Solved (stateEquiv (representativeCode 3211)) := by
  have he : stateEquiv (representativeCode 3211) = arep3211State := by decide +kernel
  rw [he]
  exact arep3211_solved

theorem anchorEntry1821_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 1821))) := by
  have he : anchorRepresentative 1821 = 3211 := by decide +kernel
  rw [he]
  exact arep3211_representative

def arep3212State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 1),some (directionEquiv 29)]

def arep3212Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,1,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ)),(9,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 6, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1),(8,(⟨(0),(1)⟩ : GZ)),(10,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3212Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 1 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3212Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3212Node0Reductions arep3212Node0Children

theorem arep3212_cached_checked :
    arep3212Node0.check (cachedIntegerProblem arep3212State) (integerInitialRows arep3212State) = true := by
  decide +kernel

theorem arep3212_checked :
    arep3212Node0.check (integerProblem arep3212State) (integerInitialRows arep3212State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3212_cached_checked

theorem arep3212_solved : Solved arep3212State :=
  solved_of_integer_certificate arep3212State arep3212Node0 arep3212_checked

theorem arep3212_representative : Solved (stateEquiv (representativeCode 3212)) := by
  have he : stateEquiv (representativeCode 3212) = arep3212State := by decide +kernel
  rw [he]
  exact arep3212_solved

theorem anchorEntry1822_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 1822))) := by
  have he : anchorRepresentative 1822 = 3212 := by decide +kernel
  rw [he]
  exact arep3212_representative

def arep3213State : DirectionTriple := ![some (directionEquiv 18),some (directionEquiv 1),some (directionEquiv 30)]

def arep3213Node0Reductions : Fin 48 → Reduction 4 :=
  ![{ rows := [![0,0,1,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(1)⟩ : GZ)),(8,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(-1),(0)⟩ : GZ)),(8,1),(9,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(-1),(0)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,(⟨(0),(-1)⟩ : GZ)),(7,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,1)] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(5,1),(8,(⟨(-1),(0)⟩ : GZ)),(9,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(-1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 4, weights := [(5,1),(7,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(4,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } },
    { rows := [![1,0,0,0]], witnesses := fun i => ([{ denominator := 2, weights := [(6,(⟨(0),(1)⟩ : GZ))] }] : List Witness).getD i.val { denominator := 1, weights := [] } }]

def arep3213Node0Children : Fin 48 → Certificate 4 64 60 48 960 :=
  ![.dead 2 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] },
    .dead 0 { denominator := 1, weights := [(0,1)] }]

def arep3213Node0 : Certificate 4 64 60 48 960 :=
  .split 4 arep3213Node0Reductions arep3213Node0Children

theorem arep3213_cached_checked :
    arep3213Node0.check (cachedIntegerProblem arep3213State) (integerInitialRows arep3213State) = true := by
  decide +kernel

theorem arep3213_checked :
    arep3213Node0.check (integerProblem arep3213State) (integerInitialRows arep3213State) = true := by
  rw [←cachedIntegerProblem_eq]
  exact arep3213_cached_checked

theorem arep3213_solved : Solved arep3213State :=
  solved_of_integer_certificate arep3213State arep3213Node0 arep3213_checked

theorem arep3213_representative : Solved (stateEquiv (representativeCode 3213)) := by
  have he : stateEquiv (representativeCode 3213) = arep3213State := by decide +kernel
  rw [he]
  exact arep3213_solved

theorem anchorEntry1823_solved : Solved (stateEquiv (representativeCode (anchorRepresentative 1823))) := by
  have he : anchorRepresentative 1823 = 3213 := by decide +kernel
  rw [he]
  exact arep3213_representative

theorem anchorBatch113 (i : Fin 16) :
    Solved (stateEquiv (representativeCode (anchorRepresentative (Fin.ofNat 2222 (16*113+i.val))))) := by
  fin_cases i
  · exact anchorEntry1808_solved
  · exact anchorEntry1809_solved
  · exact anchorEntry1810_solved
  · exact anchorEntry1811_solved
  · exact anchorEntry1812_solved
  · exact anchorEntry1813_solved
  · exact anchorEntry1814_solved
  · exact anchorEntry1815_solved
  · exact anchorEntry1816_solved
  · exact anchorEntry1817_solved
  · exact anchorEntry1818_solved
  · exact anchorEntry1819_solved
  · exact anchorEntry1820_solved
  · exact anchorEntry1821_solved
  · exact anchorEntry1822_solved
  · exact anchorEntry1823_solved

end
end Holant.Pauli.ExoticKlein.SixPort
