use {super::*, std::num::TryFromIntError};

#[derive(Debug, PartialEq, Copy, Clone, Hash, Eq, Ord, PartialOrd)]
pub struct RuneId {
  pub(crate) height: u32,
  pub(crate) index: u16,
}

impl TryFrom<u128> for RuneId {
  type Error = TryFromIntError;

  fn try_from(n: u128) -> Result<Self, Self::Error> {
    let n = n & 0xFFFF_FFFF_FFFF;
    Ok(Self {
      height: u32::try_from(n >> 16)?,
      index: u16::try_from(n & 0xFFFF).unwrap(),
    })
  }
}

impl From<RuneId> for u128 {
  fn from(id: RuneId) -> Self {
    u128::from(id.height) << 16 | u128::from(id.index)
  }
}

impl Display for RuneId {
  fn fmt(&self, f: &mut Formatter) -> fmt::Result {
    write!(f, "{}:{}", self.height, self.index,)
  }
}

impl FromStr for RuneId {
  type Err = crate::Error;

  fn from_str(s: &str) -> Result<Self, Self::Err> {
    let (height, index) = s
      .split_once(':')
      .ok_or_else(|| anyhow!("invalid rune ID: {s}"))?;

    Ok(Self {
      height: height.parse()?,
      index: index.parse()?,
    })
  }
}

pub struct DeserializeFromStr<T: FromStr>(pub T);

impl<'de, T: FromStr> DeserializeFromStr<T>
where
  T::Err: Display,
{
  pub fn with<D>(deserializer: D) -> Result<T, D::Error>
  where
    D: Deserializer<'de>,
  {
    Ok(DeserializeFromStr::<T>::deserialize(deserializer)?.0)
  }
}

impl<'de, T: FromStr> Deserialize<'de> for DeserializeFromStr<T>
where
  T::Err: Display,
{
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: Deserializer<'de>,
  {
    Ok(Self(
      FromStr::from_str(&String::deserialize(deserializer)?).map_err(serde::de::Error::custom)?,
    ))
  }
}

impl Serialize for RuneId {
  fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
  where
    S: Serializer,
  {
    serializer.collect_str(self)
  }
}

impl<'de> Deserialize<'de> for RuneId {
  fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
  where
    D: Deserializer<'de>,
  {
    DeserializeFromStr::with(deserializer)
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn rune_id_to_128() {
    assert_eq!(
      0b11_0000_0000_0000_0001u128,
      RuneId {
        height: 3,
        index: 1,
      }
      .into()
    );
  }

  #[test]
  fn display() {
    assert_eq!(
      RuneId {
        height: 1,
        index: 2
      }
      .to_string(),
      "1/2"
    );
  }

  #[test]
  fn from_str() {
    assert!("/".parse::<RuneId>().is_err());
    assert!("1/".parse::<RuneId>().is_err());
    assert!("/2".parse::<RuneId>().is_err());
    assert!("a/2".parse::<RuneId>().is_err());
    assert!("1/a".parse::<RuneId>().is_err());
    assert_eq!(
      "1/2".parse::<RuneId>().unwrap(),
      RuneId {
        height: 1,
        index: 2
      }
    );
  }

  #[test]
  fn try_from() {
    assert_eq!(
      RuneId::try_from(0x060504030201).unwrap(),
      RuneId {
        height: 0x06050403,
        index: 0x0201
      }
    );

    assert!(RuneId::try_from(0x07060504030201).is_err());
  }
}
