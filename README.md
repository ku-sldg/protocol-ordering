<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Attestation Protocol Ordering






Coq library for ordering attestation protocols by their difficulty to attack. 
Given the sets of all possible attacks on two attestation protocols, determines 
which protocol is better.

## Meta

- Author(s):
  - Sarah Johnson
  - Anna Fritz
  - Perry Alexander
- License: [GNU GENERAL PUBLIC LICENSE VERSION 2](LICENSE)
- Compatible Coq versions: 8.20 or later
- Additional dependencies: none
- Coq namespace: `AttestationProtocolOrdering`
- Related publication(s): none

## Building and installation instructions
Compile all the definitions and proof scripts with:
``` shell
make
```

Optionally, install a local version of the library with:
``` shell
make install
```

## Documentation
To order two attestation protocols, first generate all possible attacks. Attacks should be in an abstract form: 
directed graph where nodes are either measurement events or adversarial corruption/repair events and 
edges are chronological time. We recommend using the Chase model finder to enumerate all possible 
attacks on an attestation protocol specified in the Copland domain-specific language. For examples using 
Chase with the AttestationProtocolOrdering library, please see the ProtocolOrderingExamples repository at 
git@github.com:ku-sldg/protocol-ordering-examples.git. 

The function `order_fix` decidably determines the ordering relationship between two attestation protocols 
specified by their sets of attacks returning either `equiv` if they are equally difficult to attack, `leq` if the
first protocol is easier to attack, `geq` if the first protocol is harder to attack, or `incomparable` if an ordering
cannot be determined between them. 

## File Contents
* `attackgraph.v` : attack graph data structure definition
* `attackgraph_normalization.v` : attack graph normalization procedure
* `attackgraph_adversary.v` : sets of adversary events and time-constrained adversary events
* `attackgraph_ordering.v` : equivalence and partial order relations over attack graphs
* `set_minimization.v` : reduces set of attack graphs to its minimal (i.e., easiest) elements
* `set_ordering.v` : equivalence and partial order relations over sets of attack graphs
* `set_relationship.v` : ordering relationship options
