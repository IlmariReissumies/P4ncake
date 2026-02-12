# P4ncake

The goal of this repository is to develop—and eventually verify—a compiler from P4 to Pancake.

To get going:

1. Grab and build a checkout of [HOL4](https://github.com/HOL-Theorem-Prover/HOL). I used the current `master` at time of writing (`b725f6e`)
2. Grab a checkout of [CakeML](https://github.com/CakeML/cakeml). I used the current `master` at the time of writing (`8ed9c236`)
3. Grab a checkout of [HOL4P4](https://github.com/kth-step/HOL4P4). I used the current head of the `dev_hol4p4exe` branch (`cb1ecdc9`).
4. Define the environment variables `CAKEMLDIR` and `HOL4P4DIR` to point to the directories where you checked out CakeML and HOL4P4, respectively. I added lines like these to my `.bashrc`:

```
export CAKEMLDIR=/<path>/<to>/cakeml
export HOL4P4DIR=/<path>/<to>/HOL4P4
```
5. In the `P4ncake` directory, run `Holmake -k`
