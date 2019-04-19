# Halfbrown HashMap &emsp; [![Build Status]][circleci.com] [![Windows Build Status]][appveyor.com] [![Latest Version]][crates.io]

[Build Status]: https://circleci.com/gh/Licenser/halfbrown/tree/master.svg?style=svg
[circleci.com]: https://circleci.com/gh/Licenser/halfbrown/tree/master
[Windows Build Status]: https://ci.appveyor.com/api/projects/status/0kf0v6hj5v2gite9?svg=true
[appveyor.com]: https://ci.appveyor.com/project/Licenser/halfbrown
[Latest Version]: https://img.shields.io/crates/v/simd-json.svg
[crates.io]: https://crates.io/crates/simd-json

**Hashmap implementation that dynamically switches from a vector based backend to a hashbrown based backend as the number of keys grows **

---

Halfbrown, is a hashmap implementation that uses two backends to optimize for different cernairos:

## VecMap

For less then 32 key value pairs it uses a dumb vector based map implementation. This trades the need to iterator through the
vector for not having to hash strings on lookup or inserts.

## Hashbrown

For more then 32 elements it upgrades the map to aq hashbrown base map to account for longer itteration times.

## License

halfbrown itself is licensed under either of

* Apache License, Version 2.0, (LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0)
* MIT license (LICENSE-MIT or http://opensource.org/licenses/MIT)
at your option.
