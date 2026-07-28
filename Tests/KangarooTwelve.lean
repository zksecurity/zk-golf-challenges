import Challenge.Specs.KangarooTwelve
import Challenge.Utils.F2Bits

namespace Specs.KangarooTwelve.Tests

open Challenge.F2Bits

def bytesToState (bytes : Vector ℕ 200) : State (F p2) :=
  Vector.ofFn fun i : Fin stateBits =>
    have h : i.val / 8 < 200 := by
      have hi : i.val < stateBits := i.isLt
      unfold stateBits laneBits lanes at hi
      omega
    if natBit (bytes.get ⟨i.val / 8, h⟩) (i.val % 8) = 0 then 0 else 1

def stateToLanes (state : State (F p2)) : Vector ℕ 25 :=
  toWords 64 25 state

structure PermutationVector where
  input : Vector ℕ 200
  outputLanes : Vector ℕ 25

/-!
Full-state Keccak-p[1600,12] vectors generated with `KP` from the official
XKCP/K12 Python reference:
<https://github.com/XKCP/K12/blob/f95b0b73e29fe75fe99fbbb24c8000d9fcf0b40e/Python/TurboSHAKE.py>.

Outputs are represented as 25 little-endian 64-bit lanes to keep the table
compact while checking all 1600 output bits.
-/
def permutationVectors : Vector PermutationVector 8 := #v[
  {
    input := Vector.replicate 200 0
    outputLanes := #v[
      0x8e5e5438b9a78617, 0xd9cd6a50f259d01e, 0x87b8e7c652a91f35, 0x1093e067cde4e0c5,
      0xb033ab90f2d95a45, 0xe0a72f72a8dd1a45, 0xc53780aa14672f9c, 0x3edd47f50051071d,
      0xb3a31d310c178acc, 0x79b586a59257aaa0, 0xbc4a7c3db3b1f99b, 0x68874063e68a6793,
      0x5c6c03332e0e2566, 0x9caa1202b9f030da, 0x5f3b9a782bcf7a9f, 0xe536c1e061ae7923,
      0x6de9b618b73c87ec, 0x2abed1f170918ac2, 0x6aabbd53daed24b7, 0xbfc1416a2c2ee15a,
      0xc6cfe036b90952af, 0x45503617dc7060d7, 0x625611b2c29f7ae4, 0xd43671db2c30647a,
      0xcffd0d76222ca01c
    ]
  },
  {
    input := Vector.ofFn fun i : Fin 200 => i.val % 251
    outputLanes := #v[
      0x9f9081dc43edeaf4, 0x6e9859967ddc965e, 0x61fed0092014c85a, 0x1bee0f6dd5dfb472,
      0x2ea37cc9442f4394, 0x54d6f87182fe877d, 0x596c8aa0ded64b0b, 0x2b52d420abc5ecf8,
      0xa668ae64043541d8, 0x577af6e4dcf2cf76, 0xddcbdb57ccd025ba, 0xd6e351d75858297c,
      0x5d7bb1b361a75167, 0x1c9cf0f979878ebf, 0x114d3fa3b38876c1, 0x9c405210d2010002,
      0xa7a9de9991488106, 0x74d11abee6b8f8d3, 0xacd595db84d99014, 0xa514db3e29d000c9,
      0x2b8ec11d6ccd05c8, 0x6694ecc291d77e45, 0x8d3f77c18024441e, 0x2102e74d7494f974,
      0x8f1744709b129428
    ]
  },
  {
    input := Vector.replicate 200 0xff
    outputLanes := #v[
      0x15297a846e778d19, 0xfd97dc4e53b643a2, 0x909ab544ff7b8af2, 0xaf6a3bb6970cd279,
      0xeb04d1f2a613b4a5, 0xe292b679f0c22fde, 0xba9025d7165e636b, 0xd627a06456877cf7,
      0xa695c15f8d40f4ff, 0xec79de910b448c3c, 0x72b65d4ada135bb6, 0x4a50b8d07089e32d,
      0xc5494f13d05d62b6, 0x9f598b0e4bd7e121, 0x5ea0ec051b7a4434, 0x999840aec426a972,
      0xb1709cea9a97edd8, 0x60db110fd147be31, 0x563c847866d673a9, 0x23b95ac15de1f3ec,
      0xe5af93f678c9e858, 0xcef10204b3910b3a, 0xcf83a7b3639d0718, 0x0f40b8b428b7ddca,
      0xc5b689843447c82f
    ]
  },
  {
    input := Vector.ofFn fun i : Fin 200 => if i.val % 2 = 0 then 0xaa else 0x55
    outputLanes := #v[
      0x5cf6986af1df4bb4, 0xc1c4fa6b8400cf69, 0xbea024ec533c372f, 0x19af4a9590ba218e,
      0x8dba60ab5775b062, 0x5c7fe24481420a2b, 0xe2f5cdd1c55db66a, 0x409464eb32053aea,
      0xabe9143094c825a3, 0x9b191c6cfe06ad77, 0x299b2ef7ca0fbd0c, 0x77196c57f7f404b2,
      0x3c8ff8c4308b68be, 0xf93fa35cd1c494e7, 0x126dee1ba8d6067b, 0xb214e8e2ab9f81fd,
      0xe4c7beb7643fd261, 0x491976eb68ead9b7, 0x36e2bafcee435200, 0x500243ce00ab2bbd,
      0x3cb2a89e292821b6, 0xcd28823245199e14, 0x50a174c775801668, 0x7e55b52194e52467,
      0x6980c52a1caf25f8
    ]
  },
  {
    input := Vector.ofFn fun i : Fin 200 => if i.val = 0 then 1 else 0
    outputLanes := #v[
      0xfe875b2b3f4698e4, 0xa1ec11e2941a5fb3, 0xcf2af702fb5af2fb, 0xad879bf48037bb47,
      0x53350afdc7674217, 0x098bcb92f6dfd799, 0x3ff7b0d206f7ce41, 0xeaa3b3e872e4a2ff,
      0x74955899640fe594, 0x3e18d15c43360c26, 0xdd249ecda76815ea, 0x4e677a8dc249d2d7,
      0x7eda2dd47e820d5c, 0x4a228d523a660e7d, 0x7c0722d0a642b17a, 0xc933598cbc308344,
      0xc38448aaf387dec4, 0x134e225124aaa9f8, 0x214a67446cb83e33, 0x8e3f50259dc75b6f,
      0x7ebc2d3b3c9480ef, 0x08e1035111058758, 0xd19db2b90476cc3d, 0x88c9e657697b1b4e,
      0x5ce6801807bab570
    ]
  },
  {
    input := Vector.ofFn fun i : Fin 200 => if i.val = 199 then 0x80 else 0
    outputLanes := #v[
      0x31e6bf25c8dd985a, 0x2e74d9d489f6dcc0, 0xb33b95d727b6a261, 0xe69449340e435bf2,
      0x37c7edc67ea5a4c2, 0x9ba2ad509147dc4c, 0x2259a12a7216d2ce, 0xc807909638a3644a,
      0xdfa781a5ce92a511, 0x06da0a178caea30b, 0x7b6f0702cec53330, 0x2f6e90a51a638516,
      0x6e592e74d8965f41, 0x189c97d10f594a0e, 0x255e5cb50878a76f, 0x507aa5707a01c90e,
      0x513f942933de074e, 0x60eeb135063e391d, 0x5ba478471ac14374, 0x73f034bf30242fc2,
      0x301c2a305185d495, 0x6e11aa881167b6ce, 0x4c52c1ea74e14f3e, 0xbcfd7570ff867495,
      0xe52da69d70b7b8d0
    ]
  },
  {
    input := Vector.ofFn fun i : Fin 200 => (73 * i.val + 41) % 256
    outputLanes := #v[
      0xb52771fefa59b527, 0xb17dcb89cf6b0fbf, 0xf8da6ce5f5f67d35, 0x9b5d96bcc3ab8e8c,
      0x5f2f38a5628dc599, 0x3d42415fc6ad093f, 0x6efb77bf2b8029b1, 0xf230fd92b59be04a,
      0x1b47225a24c4f4a8, 0xddc0640d2d353890, 0xb0fa869283db9180, 0xa7a474b6582289a5,
      0x60d37a8c8bdfb2ad, 0x831b8bf459a628c6, 0x70cb622bc2ef21f2, 0xdbbc721b8e2d6faa,
      0x8b8af3dbc27a372c, 0xec204a44541bf561, 0x9f726aeaf19f70a8, 0x4eff2cdfe3326fa2,
      0xf0e44eb28e607e0f, 0xb051dfa0a25bb636, 0xbddcb865030cc1bf, 0x9961e45da82eaf81,
      0x30f1490b442317ec
    ]
  },
  {
    input := Vector.ofFn fun i : Fin 200 =>
      (i.val * i.val + 17 * i.val + 29) % 256
    outputLanes := #v[
      0x66f93bb7690d253d, 0xc7bc64959f1054d4, 0x01c7502de286295c, 0xe16ede052e5b7af4,
      0x47879c6816d91c7e, 0xe300d7940e07a942, 0xad1bf54ed6bb2bbe, 0x94116ec4f9de7a3c,
      0xf76b6eaf1c8da704, 0x4c62ec433193b307, 0xf6a3df598745f9fc, 0xa455f9e09591e4cc,
      0xf3e808ec9691fe7f, 0xf8c3662ec583fde7, 0x3823e3fbb6a05069, 0xf6b22f54e62d633e,
      0x22f594ef87ded299, 0x4fd89b3ccc38717e, 0x8bce6e413ea17cab, 0xdb0739a2033ced36,
      0x884b0307570a2e69, 0x0fab5ecad2650cc3, 0x330980df6a68efeb, 0xc8848098450e7e2e,
      0xf8c5f00d03350cde
    ]
  }
]

example : roundConstants = #v[
  0x000000008000808B,
  0x800000000000008B,
  0x8000000000008089,
  0x8000000000008003,
  0x8000000000008002,
  0x8000000000000080,
  0x000000000000800A,
  0x800000008000000A,
  0x8000000080008081,
  0x8000000000008080,
  0x0000000080000001,
  0x8000000080008008
] := by native_decide

example : ∀ i : Fin 8,
    let v := permutationVectors[i]
    stateToLanes (keccakP1600_12 (bytesToState v.input)) = v.outputLanes := by
  native_decide

end Specs.KangarooTwelve.Tests
