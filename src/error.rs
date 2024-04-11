use ariadne::{Color, Label, Report, ReportKind};

use crate::lex::Span;

// message, reason, pos
#[derive(Debug)]
pub struct GenericError(pub String, pub String, pub Span);

impl GenericError {
    pub fn report(
        &self,
        filename: impl Into<String>,
    ) -> Report<'static, (String, std::ops::Range<usize>)> {
        let filename: String = filename.into();
        Report::build(ReportKind::Error, filename.clone(), self.2.start)
            .with_message(self.0.clone())
            .with_label(
                Label::new((filename.clone(), self.2.into_range()))
                    .with_message(self.1.clone())
                    .with_color(Color::Red),
            )
            .finish()
    }
}
