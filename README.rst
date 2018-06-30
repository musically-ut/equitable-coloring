========
Overview
========

.. start-badges

.. list-table::
    :stub-columns: 1

    * - docs
      - |docs|
    * - tests
      - | |travis|
        | |codecov|
    * - package
      - | |version| |wheel| |supported-versions| |supported-implementations|
        | |commits-since|

.. |docs| image:: https://readthedocs.org/projects/equitable-coloring/badge/?style=flat
    :target: https://readthedocs.org/projects/equitable-coloring
    :alt: Documentation Status

.. |travis| image:: https://travis-ci.org/musically-ut/equitable-coloring.svg?branch=master
    :alt: Travis-CI Build Status
    :target: https://travis-ci.org/musically-ut/equitable-coloring

.. |codecov| image:: https://codecov.io/github/musically-ut/equitable-coloring/coverage.svg?branch=master
    :alt: Coverage Status
    :target: https://codecov.io/github/musically-ut/equitable-coloring

.. |version| image:: https://img.shields.io/pypi/v/equitable-coloring.svg
    :alt: PyPI Package latest release
    :target: https://pypi.python.org/pypi/equitable-coloring

.. |commits-since| image:: https://img.shields.io/github/commits-since/musically-ut/equitable-coloring/v0.1.1.svg
    :alt: Commits since latest release
    :target: https://github.com/musically-ut/equitable-coloring/compare/v0.1.1...master

.. |wheel| image:: https://img.shields.io/pypi/wheel/equitable-coloring.svg
    :alt: PyPI Wheel
    :target: https://pypi.python.org/pypi/equitable-coloring

.. |supported-versions| image:: https://img.shields.io/pypi/pyversions/equitable-coloring.svg
    :alt: Supported versions
    :target: https://pypi.python.org/pypi/equitable-coloring

.. |supported-implementations| image:: https://img.shields.io/pypi/implementation/equitable-coloring.svg
    :alt: Supported implementations
    :target: https://pypi.python.org/pypi/equitable-coloring


.. end-badges

Equitable coloring for networkX graphs.

* Free software: MIT license

Installation
============

::

    pip install equitable-coloring

Documentation
=============

https://equitable-coloring.readthedocs.io/

Development
===========

To run the all tests run::

    pip install pytest-cov  # Needed the first time.
    python setup.py test
