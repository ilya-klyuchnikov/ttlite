Error handling of translation
------------------------------

This directory contains tests for graceful handling of error of translation from meta-syntax to abstract syntax.

**TODO**: Some type-checking errors should be moved to errors of translations:

* Unknown identifier
* redefined identifier (right now identifier may be redefined)
* More detailed error message on not saturated eliminators
* Messages on not saturated constructor applications
