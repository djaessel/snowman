#include "classanalyzer.h"

ClassAnalyzer::ClassAnalyzer()
{
  QString endlDir = QString("./endl").replace("/", QDir::separator());
  QString endlClassInfoDir = QString("./endl/class_info").replace("/", QDir::separator());
  if (!QDir(endlDir).exists())
    QDir().mkdir(endlDir);
  if (!QDir(endlClassInfoDir).exists())
    QDir().mkdir(endlClassInfoDir);
}

QString ClassAnalyzer::clamsFix(QString allText, QString text)
{
  int clam = 0;
  bool lok = false;

  for (int i = 0; i < text.length(); i++) {
      QChar c = text.at(i);
      if (c == '('){
          clam++;
          lok = true;
      } else if (c == ')') {
          clam--;
      }
  }

  QString tx = text.remove(QRegExp("([\n]+$)")).trimmed();
  QString xon = allText.mid(allText.indexOf(tx) + tx.length());

  for (int i = 0; i < xon.length(); i++) {
      QChar c = xon.at(i);
      if (c == '('){
          clam++;
      } else if (c == ')') {
          clam--;
      }

      tx += c;
      if (clam <= 0) break;
  }

  QString revTx;
  while (clam < 0) {
      tx.reserve(tx.length());
      revTx = QString(tx);
      tx.reserve(tx.length());
      int lastIndex = tx.length() - revTx.indexOf(")") - 1;
      tx = tx.left(lastIndex);
      clam++;
  }

  tx = tx.remove(QRegExp("([;]$)"));
  lok = (lok && tx.at(tx.length() - 1) != ')');
  if (lok) {
      tx.reserve(tx.length());
      revTx = QString(tx);
      tx.reserve(tx.length());
      int x = 0;

      for (int i = 0; i < revTx.length(); i++) {
          QChar c = revTx.at(i);
          if (c == ')'){
              break;
          }
          x++;
      }

      tx = tx.left(tx.length() - x);
  }

  return tx;
}

void ClassAnalyzer::benulf(QString line, map<QString, FixedClass>* classes, map<QString, QString> *classAttributes, QString cls, QString orgCls, QString func, QString fragger)
{
  QString tmo = line.remove(QRegExp("([\n]+$)"));
  if (tmo.contains("//")) {
      tmo = tmo.left(tmo.indexOf("//"));
  }

  QRegExp mo("([*]*[\(]*\("+fragger+"[ +]*[^a-zA-Z0-9]+[ [+][*]\\[\\]\\(\\)x0-9a-zA-Z]+\\)[\\)]*)");
  mo.indexIn(tmo);

  QRegExp mo2("([ ]"+fragger+"[ +]*[ \\;][ [+][*]\\[\\]\\(\\)x0-9a-zA-Z=]*)");
  mo2.indexIn(tmo);

  QRegExp mo3("(STRUCT_[0-9*]+ [a-z0-9_]+ [=] "+fragger+"[;])");
  mo3.indexIn(tmo);

  QString tx;
  QString nomo("");
  if (mo.captureCount() > 0) {
      tx = this->clamsFix(tmo, mo.cap());
      nomo = "\"" + tx + "\";\"" + tmo.trimmed().remove(QRegExp("([;]+$)"));
  } else if (mo2.captureCount() > 0) {
      tx = this->clamsFix(tmo, mo2.cap());
      nomo = "\"" + tx + "\";\"" + tmo.trimmed().remove(QRegExp("([;]+$)"));
  } else if (tmo.contains(fragger + "*") ||
             tmo.contains(fragger + " ") ||
             (fragger == QString("rdi") && tmo.contains("this->"))) {
      bool ok = true;
      if (fragger == QString("rdi") && tmo.contains("this->")) {
        QString searchX = tmo.mid(tmo.indexOf("this->") + 6).split('(').first();
        foreach (FixedFunction f, classes->at(cls).getFunctions()) {
            if (f.getName() == searchX) {
                ok = false;
            }
        }
      }
      if (ok) {
          nomo = "\"" + fragger + "\";\"" + tmo.trimmed().remove(QRegExp("([;]$)"));
      }
  }

  if (nomo.length() > 0) {
      nomo += "\";\"" + cls + "\";\"" + func + "\"\n";
      QString key = nomo.split(';').first();
      if (classAttributes->count(key) == 0) {
          classAttributes->insert_or_assign(key, nomo);
      }
  }

  if (mo3.captureCount() > 0) {
      QString xa = tmo.mid(tmo.indexOf("STRUCT_"));
      xa = xa.left(xa.indexOf(" "));
      nomo = "\"" + xa + "\";\"" + tmo.trimmed().remove(QRegExp("([;]+$)")) + "\";\"" + cls + "\";\"" + func + "\"\n";
      QString key = nomo.split(';').first();
      if (classAttributes->count(key) == 0) {
          classAttributes->insert_or_assign(key, nomo);
      }
  }
}

QStringList ClassAnalyzer::findClassAttributesExternal(QString cls, map<QString, FixedClass> *classes)
{
  map<QString, QString> classAttributes;
  vector<FixedFunction> myFuncs = classes->at(cls).getFunctions();

  foreach (auto clsx, *classes) {
      if (clsx.first == cls) continue; // skip same class

      foreach (FixedFunction func, clsx.second.getFunctions()) {
          QStringList activeAttribs;
          foreach (QString line, func.getCodeLines()) {
              QString tmo = line.remove(QRegExp("([\n]+$)"));
              if (tmo.contains("//")) {
                  tmo = tmo.left(tmo.indexOf("//"));
              }

              if (tmo.contains(cls)) {
                  QRegExp moa("( "+cls+"[*]* [a-z0-9_]+ = )");
                  moa.indexIn(tmo);

                  QRegExp mob("( "+cls+"[*]* [a-z0-9_]+[;])");
                  mob.indexIn(tmo);

                  QRegExp mo2("([a-z0-9_]+[-][>][a-zA-Z_<>0-9*]+\()");
                  mo2.indexIn(tmo);

                  QString tx;
                  QString nomo("");
                  if (moa.captureCount() > 0 || mob.captureCount() > 0) {
                      if (moa.captureCount() > 0) {
                          tx = moa.cap().trimmed().remove(QRegExp("([=]+$)")).remove(QRegExp("([ ]+$)"));
                      } else {
                          tx = mob.cap().trimmed().remove(QRegExp("([;]+$)"));
                      }
                      tx = tx.split(' ')[1];
                      activeAttribs.append(tx);
                      nomo = "\"" + tx + "\";\"" + tmo.trimmed().remove(QRegExp("([;]+$)"));
                  } else if (mo2.captureCount() > 0) {
                      tx = mo2.cap().trimmed();
                      QString txa = tx.mid(tx.indexOf('>') + 1);
                      txa = txa.left(txa.indexOf('(')- 1); // FIXME: possible inde bug because txa was tx before in python
                      foreach (auto f, myFuncs) {
                          if (f.getName() == txa) {
                              nomo = "\"" + tx.split('(').first() + "\";\"" + tmo.trimmed().remove(QRegExp("([;]+$)"));
                              break;
                          }
                      }
                  }

                  if (nomo.length() > 0) {
                      nomo += "\";\"" + clsx.first + "\";\"" + func.getName() + "\"\n";
                      QString key = nomo.split(';').first();
                      if (classAttributes.count(key) == 0) {
                          classAttributes.insert_or_assign(key, nomo);
                      }
                  } else {
                      foreach (QString frag, activeAttribs) {
                          this->benulf(line, classes, &classAttributes, clsx.first, cls, func.getName(), frag);
                      }
                  }
              } else {
                  foreach (QString frag, activeAttribs) {
                      this->benulf(line, classes, &classAttributes, clsx.first, cls, func.getName(), frag);
                  }
              }
          }
      }
  }

  // TODO: remove these later when attribs found!
  QFile f(QString("./endl/" + cls + ".endl").replace("/", QDir::separator()));
  if (f.open(QFile::WriteOnly | QFile::Text)) {
      QTextStream out(&f);
      foreach (auto attr, classAttributes) {
          out << attr.second << Qt::endl;
      }
      f.close();
  }

  QStringList ret;
  foreach (auto attr, classAttributes) {
      ret.append(attr.second);
  }
  classAttributes.clear();

  return ret;
}

QStringList ClassAnalyzer::findClassAttributes(QString cls, map<QString, FixedClass> *classes)
{
  map<QString, QString> classAttributes;
  foreach (FixedFunction func, classes->at(cls).getFunctions()) {
      foreach (QString line, func.getCodeLines()) {
          this->benulf(line, classes, &classAttributes, cls, cls, func.getName());
      }
  }

  QFile f(QString("./endl/" + cls + ".endl").replace("/", QDir::separator()));
  if (f.open(QFile::WriteOnly | QFile::Text)) {
      QTextStream out(&f);
      foreach (auto attr, classAttributes) {
          out << attr.second << Qt::endl;
      }
      f.close();
  }

  QStringList ret;
  foreach (auto attr, classAttributes) {
      ret.append(attr.second);
  }
  return ret;
}

map<QString, QStringList> ClassAnalyzer::findClassAttributes(map<QString, FixedClass> *classes)
{
  map<QString, QStringList> classAttributes;

  cout << "Add used class imports..." << endl;

  uint processor_count = processorCount();
  int length = classes->size() / processor_count;
  for (uint i = 0; i < processor_count; i++) {
      int start = i * length;
      int end = start + length;
      if (i == processor_count - 1)
          end = classes->size();

      ClassAnalyzerTask *hello = new ClassAnalyzerTask(this, &classAttributes, classes, start, end);
      // QThreadPool takes ownership and deletes 'hello' automatically
      QThreadPool::globalInstance()->start(hello);
  }
  QThreadPool::globalInstance()->waitForDone(); // waits for all to be done(?)

  cout << "DONE" << endl;

  return classAttributes;
}
