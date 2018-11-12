# utils: a function to show latex printed objects in the notebook
# useful to show objects on a Jupyter notebook
# on a local Sage instal, just use view(objects)
from sage.misc.latex import _Latex_prefs
from sage.misc.latex import png
from sage.misc.temporary_file import tmp_filename
import os
from IPython.display import Image
from IPython.display import display

def viewLatex(objects):
    engine = _Latex_prefs._option["engine"]
    if type(objects) != list:
        objects = [objects]
    L = []
    for o in objects:
        file_name = tmp_filename() + ".png"
        png(o, file_name, debug = False, engine = engine)
        L.append(Image(filename = file_name))
    return display(*L)
