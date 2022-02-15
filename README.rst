========
Overview
========

**Update**: This is now merged into ``networkx`` package (via `networkx/#3127 <https://github.com/networkx/networkx/pull/3127>`_). See `networkx.algorithms.coloring.equitable_color <https://networkx.org/documentation/stable/reference/algorithms/generated/networkx.algorithms.coloring.equitable_color.html>`_.

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

.. |commits-since| image:: https://img.shields.io/github/commits-since/musically-ut/equitable-coloring/v0.1.2.svg
    :alt: Commits since latest release
    :target: https://github.com/musically-ut/equitable-coloring/compare/v0.1.2...master

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

Equitable coloring for networkX_ graphs.

.. _networkX: https://networkx.github.io/

From Wikipedia_:

    In graph theory [..] an equitable coloring is an assignment of colors to the vertices of an undirected graph, in such a way that

    + No two adjacent vertices have the same color, and
    + The numbers of vertices in any two color classes differ by at most one.


`Kierstead et. al. <https://link.springer.com/article/10.1007%2Fs00493-010-2483-5>`_ have provided a fast polynomial time algorithm for uncovering an equitable coloring using ``r + 1`` colors for a graph with maximum degree ``r``.
This package is an implementation of the algorithm for networkX graphs.

.. _Wikipedia: https://en.wikipedia.org/wiki/Equitable_coloring

* Free software: MIT license

Installation
============

::

    pip install equitable-coloring


Usage
=====

To use ``equitable-coloring``::

        >>> import networkx as nx
        >>> from equitable_coloring import equitable_color
        >>> from equitable_coloring.utils import is_equitable
        >>> G = nx.cycle_graph(4)
        >>> d = equitable_color(G, num_colors=3)
        >>> is_equitable(G, d)
        True


Documentation
=============

https://equitable-coloring.readthedocs.io/

Development
===========

To run the all tests run::

    pip install pytest-cov  # Needed the first time.
    python setup.py test


Or, you can use ``tox``.
