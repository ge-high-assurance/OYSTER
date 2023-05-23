FROM python:3.11-bullseye
RUN pip install scikit-learn pandas networkx tqdm
RUN pip install --upgrade gensim
COPY . /
CMD ["python", "suggest.py", "/tmp/behavior.xml", "500", "/xml_data/New_schedule", "/dataset/", "/features/nci1.csv", "/graph2vec1/src/graph2vec.py", "/tmp/suggestion.xml", "/labels", "/tmp/crv_output.xml"]

