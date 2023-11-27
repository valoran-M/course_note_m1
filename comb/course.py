#!./.env/bin/python

from travo import GitLab
from travo.jupyter_course import JupyterCourse
from travo.script import main

forge = GitLab("https://gitlab.dsi.universite-paris-saclay.fr/")
course = JupyterCourse(
                 forge=forge,
                 path="M1InfoMPRICombAlg",
                 name="Combinatoire et Calcul Algébrique",
                 student_dir="./",
                 session_path="2022-2023",
                 script="./course.py",
                 expires_at="2023-12-31",
                 jobs_enabled_for_students=False)

usage = f"""Aide pour l'utilisation de la commande {course.script}
===============================================

Télécharger ou mettre à jour un TP (remplacer «Seance1» par le nom du TP):

    cd ~/M1InfoMPRI/CombAlg
    {course.script} fetch Seance1

Déposer un TP (remplacer «Seance1» par le nom du TP):

    cd ~/M1InfoMPRI/CombAlg
    {course.script} submit Seance1


Plus d'aide:

    {course.script} --help
"""

if __name__ == "__main__":
    main(course, usage)
