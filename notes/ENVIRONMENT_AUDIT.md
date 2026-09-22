# Environment audit

Inspected on 2026-09-22 from `/home/dusty/Desktop/Marabou Verification`.

```text
$ isabelle version
Isabelle2025-2

$ command -v isabelle
/home/dusty/Desktop/Isabelle/Isabelle2025-2/bin/isabelle
```

`isabelle getenv` reported:

| Setting | Value |
| --- | --- |
| `ISABELLE_HOME` | `/home/dusty/Desktop/Isabelle/Isabelle2025-2` |
| `ISABELLE_HOME_USER` | `/home/dusty/.isabelle/Isabelle2025-2` |
| `ISABELLE_HEAPS` | `/home/dusty/.isabelle/Isabelle2025-2/heaps` |
| `ISABELLE_LOGIC` | `HOL` |
| `ML_SYSTEM` | `polyml-5.9.2` |
| `ISABELLE_JDK_HOME` | `/home/dusty/Desktop/Isabelle/Isabelle2025-2/contrib/jdk-21.0.9/x86_64-linux` |

The installation contains `bin`, `src`, `lib`, `heaps`, `contrib`, `doc`, and
`etc`. The standard launcher and `etc/settings` were inspected. No installation
settings were changed. The development imports `HOL.Real` and uses the installed
HOL session; no AFP dependency or third-party proof tool was added.

`isabelle build_log` initially failed inside the workspace sandbox with
`ClassNotFoundException: isabelle.Isabelle_Tool`. The same log-inspection command
was rerun with approved access outside the sandbox and succeeded, with no
matching error or warning entries. No installation repair was required.

The existing root repository initially had no commits and already staged
`.gitmodules` and both submodule entries. That staged work was left intact.
There were no applicable `AGENTS.md` files in the workspace or ancestor paths.

| Source | Revision inspected | Initial working tree |
| --- | --- | --- |
| `upstream/Marabou` | `1c2f4788c32e2f4e407c356b763a8025c5578722` | Clean |
| `upstream/ReluplexCav2017` | `60b482eec832c891cb59c0966c9821e40051c082` | Clean |

No fetching, source updates, upstream edits, C++ compilation, or solver runs
were necessary for this milestone. The source audit is tied to those revisions,
not to an assertion that they are the latest available revisions.
