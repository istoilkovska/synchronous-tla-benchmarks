# synchronous-tla-benchmarks
Several synchronous fault-tolerant distributed algorithms encoded in [TLA+](https://lamport.azurewebsites.net/tla/tla.html). 
These benchmarks were checked using the model checker [TLC](https://lamport.azurewebsites.net/tla/tools.html) in the following [paper](https://link.springer.com/chapter/10.1007%2F978-3-319-73721-8_1):

    Benjamin Aminof, Sasha Rubin, Ilina Stoilkovska, Josef Widder, Florian Zuleger.
    Parameterized Model Checking of Synchronous Distributed Algorithms by Abstraction.
    VMCAI 2018

This repository contains the following benchmarks: 

Name  | Problem | Reference
:-----|:--------|:---------
[edac](https://github.com/istoilkovska/synchronous-tla-benchmarks/tree/master/edac) | early deciding consensus | [Charron-Bost, Schiper](https://www.sciencedirect.com/science/article/pii/S0196677403001652)
[fair_cons](https://github.com/istoilkovska/synchronous-tla-benchmarks/tree/master/fair_cons) | consensus | [Raynal](https://www.morganclaypool.com/doi/abs/10.2200/S00294ED1V01Y201009DCT003), p.17
[floodmin](https://github.com/istoilkovska/synchronous-tla-benchmarks/tree/master/floodmin) | k-set agreement, for k=2| [Lynch](http://groups.csail.mit.edu/tds/distalgs.html), p.136
[floodset](https://github.com/istoilkovska/synchronous-tla-benchmarks/tree/master/floodset) | consensus | [Lynch](http://groups.csail.mit.edu/tds/distalgs.html), p.103
[nbac](https://github.com/istoilkovska/synchronous-tla-benchmarks/tree/master/nbac) | non-blocking atomic commit | [Raynal](https://www.morganclaypool.com/doi/abs/10.2200/S00294ED1V01Y201009DCT003), p.82
[pdif](https://github.com/istoilkovska/synchronous-tla-benchmarks/tree/master/pdif) | early stopping consensus | [Raynal](https://www.morganclaypool.com/doi/abs/10.2200/S00294ED1V01Y201009DCT003), p.38 

All of the benchmarks assume the crash fault model, where at most T of the total N processes in the system can fail by crashing, with T < N. Once a process crashes, it stops executing the algorithm and it cannot restart.

For each benchmark `name`, the directory `name` contains the following TLA+ files:
  - `name.tla` - this is a concrete encoding of the algorithm, that can be used to check the safety and liveness properties of the algorithm for small system instances, e.g., up to N = 5 processes. When checking, one needs to assign concrete values to the parameters N, T, F.
  - `name_abstract.tla` - this is an abstract encoding of the algorithm, that can be used to check the safety and liveness properties in the parameterized case, that is, for all values of the parameters N, T, F. In this encoding, the behavior of a small number M of processes (usually 2 or 3) is kept as in the concrete system, while the behavior of the remaining N - M processes is abstracted. The M processes are assumed to be correct, which implies that T <= N - M.
  - `name_abstract_m'.tla` - this is an abstract encoding that captures the corner cases where M' < M processes are fixed and assumed correct, that is, when N - M < T < N.
  
For more details, and for our experimental results, please check the [VMCAI 2018 paper](https://link.springer.com/chapter/10.1007%2F978-3-319-73721-8_1).
