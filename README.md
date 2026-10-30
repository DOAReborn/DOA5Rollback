<p align="center">
  <img src="docs/readme-banner.svg" alt="DOA5Rollback" width="720">
</p>
<p align="center">Rollback netcode for <b>Dead or Alive 5 Last Round</b> lobby matches. Needs DOA5Tools.</p>
<p align="center">
  <a href="https://github.com/DOAReborn/DOA5Rollback/releases/latest"><img src="https://img.shields.io/github/v/release/DOAReborn/DOA5Rollback?label=release" alt="release"></a>
  <a href="https://github.com/DOAReborn/DOA5Rollback/releases"><img src="https://img.shields.io/github/downloads/DOAReborn/DOA5Rollback/total" alt="downloads"></a>
  <a href="LICENSE"><img src="https://img.shields.io/github/license/DOAReborn/DOA5Rollback" alt="license"></a>
  <img src="https://img.shields.io/badge/game-DOA5%20Last%20Round-e0457b" alt="game: DOA5 Last Round">
</p>

Also: Replay Takeover (take control of a replay, offline).

## Build

Visual Studio 2019 or later (x86). From `src/`:

```
cl /nologo /std:c++17 /O2 /MT /W4 /EHsc /LD /DDOA5RB_RELEASE Rollback.cpp /link /OUT:DOA5Rollback.asi
```
