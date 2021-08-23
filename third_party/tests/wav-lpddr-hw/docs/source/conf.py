# Configuration file for the Sphinx documentation builder.
#
# This file only contains a selection of the most common options. For a full
# list see the documentation:
# https://www.sphinx-doc.org/en/master/usage/configuration.html

# -- Path setup --------------------------------------------------------------

# If extensions (or modules to document with autodoc) are in another directory,
# add these directories to sys.path here. If the directory is relative to the
# documentation root, use os.path.abspath to make it absolute, like shown here.
#
# import os
# import sys
# sys.path.insert(0, os.path.abspath('.'))

# -- Project information -----------------------------------------------------

# Template
# /prj/wavious/dev/frontend/core/workareas/sbridges/mvp_pll/dev/docs/source/conf.py

project = 'WDDR'
copyright = '2021, Wavious LLC'
author = 'Wavious LLC'

# The full version, including alpha/beta/rc tags
release = '1.0'

# -- General configuration ---------------------------------------------------

# Add any Sphinx extension module names here, as strings. They can be
# extensions coming with Sphinx (named 'sphinx.ext.*') or your custom
# ones.
extensions = ['sphinx.ext.autodoc', 'sphinx.ext.autosectionlabel', 'rst2pdf.pdfbuilder', 'docxbuilder']
pygments_style = 'sphinx'

# Add any paths that contain templates here, relative to this directory.
templates_path = ['_templates']

# The master toctree document.
master_doc = 'index'

# List of patterns, relative to source directory, that match files and
# directories to ignore when looking for source files.
# This pattern also affects html_static_path and html_extra_path.
exclude_patterns = []

# -- Options for HTML output -------------------------------------------------

# The theme to use for HTML and HTML Help pages.  See the documentation for
# a list of builtin themes.
#
#html_theme = 'alabaster'
html_theme = 'sphinx_rtd_theme'
html_logo = 'wavious_logo.png'

# Add any paths that contain custom static files (such as style sheets) here,
# relative to this directory. They are copied after the builtin static files,
# so a file named "default.css" will overwrite the builtin "default.css".
html_static_path = ['_static']

# -- Options for PDF output -------------------------------------------------
pdf_stylesheets = ['./source/rst2pdf.stylesheet.rts']

pdf_style_path = ['.']
pdf_font_path = ['/usr/share/fonts/liberation', '/usr/share/fonts/google-crosextra-carlito']

pdf_break_level = 2
pdf_breakside = 'any'
pdf_cover_template = 'cover.tmpl'
pdf_documents = [('index', u'WDDR', u'WDDR', u'Wavious'),]
