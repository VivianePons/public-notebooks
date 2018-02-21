FROM sagemath/sagemath:8.0-2

# Pdflatex

#RUN apt-get -q update && apt-get -qy dist-upgrade
RUN apt-get -qy install texlive-latex-extra texlive-fonts-recommended
#RUN apt-get -q clean

# Inspired from https://mybinder.readthedocs.io/en/latest/dockerfile.html#preparing-your-dockerfile
# Make sure the contents of our repo are in ${HOME}
COPY . ${HOME}
