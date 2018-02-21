FROM sagemath/sagemath:8.0-2

# Pdflatex

RUN sudo apt-get -q update && sudo apt-get -qy dist-upgrade
RUN sudo apt-get -qy install texlive-latex-extra texlive-fonts-recommended
RUN sudo apt-get -q clean

# Inspired from https://mybinder.readthedocs.io/en/latest/dockerfile.html#preparing-your-dockerfile
# Make sure the contents of our repo are in ${HOME}
COPY . ${HOME}
